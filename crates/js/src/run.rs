//! `stitchwort run --js` (docs/evaluator-speed.md §5): a program's `main`,
//! with everything it uses, as an ES module that Node runs.
//!
//! Two files. `program.mjs` is the generated code (the same as `build --js`
//! generates, but for what `main` uses rather than for exports), then a
//! runner that does what `stitchwort_driver`'s `run_loop` does: it steps
//! `main ()` as a partial computation, performs each `IO` operation for real
//! and replies, until the result. `run.mjs` starts `program.mjs` in a
//! worker thread with a large stack, since generated code recurses on the
//! JS stack (a loop only for tail calls), and a non-tail recursion over a
//! long list would overflow Node's default stack.
//!
//! What runs is the term `stitchwort run` runs: `main ()` checked against
//! `() -> {IO, Partial} ()`, so a total or pure `main` arrives lifted, as in
//! the Rust runner. Unlike `build --js`, a `Delay` isn't erased to a token
//! here (docs/proposals/partial.md §7.6): its constants build
//! `StitchwortDelay` objects, and the runner steps them with the machine of
//! `stitchwort_core::step`, frame for frame. JS has no tick limit and no
//! evaluation budget: a loop just loops, as with `stitchwort run`.
//!
//! The runner reports how a run failed by its exit code, with the message
//! in a file the CLI names: [`EXIT_RESOURCE`] when the program ran out of
//! the engine's stack or memory (or made a number or string too large for
//! it), [`EXIT_IO`] when reading or writing failed.

use std::fmt::Write;

use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, DefId, Globals, Limits, Term};
use stitchwort_syntax::Diagnostic;

use super::{
    CHARS_OF_TEXT, Convention, Gen, Options, RUNTIME, RUNTIME_CODECS, TEXT_AS_STRING,
    TEXT_OF_CHARS, erasable, field_key_at, js_string_literal, reachable,
};

/// The generated files.
pub struct Program {
    /// `program.mjs`: the code, and the runner.
    pub module: String,
    /// `run.mjs`: starts `program.mjs` in a worker thread. Run as
    /// `node run.mjs ERROR_FILE`.
    pub launcher: String,
}

/// The runner's exit code when the program ran out of resources.
pub const EXIT_RESOURCE: i32 = 70;
/// The runner's exit code when reading standard input or writing standard
/// output failed.
pub const EXIT_IO: i32 = 71;

/// The worker thread's stack, in megabytes. It's reserved, not used: memory
/// is taken only as deep as the program recurses. 2 GB is about ten million
/// frames of a simple recursion.
pub const STACK_MB: u32 = 2048;

/// The JS name of the continuation `\y => Done y` (see
/// [`Gen::is_done_continuation`]).
pub(crate) const DONE_K: &str = "DONE_K";

/// The JS for one of `Delay`'s constants, taking its runtime arguments
/// (its type arguments are erased; [`generate_program`] checks).
pub(crate) fn primitive_js(prim: Primitive) -> &'static str {
    match prim {
        Primitive::Now => "(v) => new StitchwortDelay(D_NOW, v, undefined)",
        Primitive::Lift => "(c) => new StitchwortDelay(D_LIFT, c, undefined)",
        Primitive::BindD => "(d) => (k) => new StitchwortDelay(D_BIND, d, k)",
        Primitive::MapSig => "(m) => (d) => new StitchwortDelay(D_MAP, m, d)",
        Primitive::Pfix => "(f) => (x) => new StitchwortDelay(D_PFIX, f, x)",
        Primitive::Delay => unreachable!("`Delay` is a type, so it's erased"),
    }
}

/// How many runtime arguments each constant takes in [`primitive_js`].
fn runtime_arity(prim: Primitive) -> usize {
    match prim {
        Primitive::Now | Primitive::Lift => 1,
        Primitive::BindD | Primitive::MapSig | Primitive::Pfix => 2,
        Primitive::Delay => 0,
    }
}

fn internal(message: String) -> Diagnostic {
    Diagnostic::error("E-EXPORT", format!("internal error: {message}"))
}

/// Generates the program that runs `main`: the closed term of type
/// `{IO, Partial} ()` that `stitchwort run` runs (`Main`'s term in the
/// driver).
pub fn generate_program(g: &Globals, limits: Limits, main: &Term) -> Result<Program, Diagnostic> {
    let _op = g.budget.operation(Limits::stack_only(limits.stack));
    erasable(g)?;
    let mut codegen = Gen::new(g, Options::default())?;
    codegen.run_delay = true;
    if codegen.text.is_none() {
        return Err(internal(
            "the prelude's `Text` doesn't have the representation `run --js` expects".into(),
        ));
    }
    let shapes = Shapes::new(g)?;

    let roots: Vec<DefId> = main
        .subterms()
        .filter_map(|(t, _)| match t {
            Term::Def(id) => Some(*id),
            _ => None,
        })
        .collect();
    let failure = std::cell::RefCell::new(None);
    let used = reachable(g, roots, |id| match codegen.try_info(id) {
        Ok(info) => {
            info.result_erased
                || codegen.kernel_native(id).is_some()
                || codegen.text_natives.contains_key(&id)
                || codegen.int_natives.contains_key(&id)
        }
        Err(e) => {
            failure.borrow_mut().get_or_insert(e);
            true
        }
    });
    if let Some(e) = failure.into_inner() {
        return Err(e);
    }
    let used: Vec<DefId> = (0..g.defs.len())
        .map(DefId)
        .filter(|id| used[id.0])
        .collect();
    for &id in &used {
        let info = codegen.try_info(id)?;
        let def = g.def(id);
        if let Some(prim) = g.builtins.primitive(id) {
            let runtime = info.mask.iter().filter(|erased| !**erased).count();
            if info.convention != Convention::Erased && runtime != runtime_arity(prim) {
                return Err(internal(format!(
                    "`{}` takes {runtime} runtime arguments, not {}",
                    def.name,
                    runtime_arity(prim)
                )));
            }
        } else if def.body.is_none() && !info.result_erased {
            return Err(Diagnostic::error(
                "E-EXPORT",
                format!("can't generate JavaScript for `{}`", def.name),
            )
            .with_label(
                def.span,
                "it hasn't been checked successfully, so it has no definition to generate",
            ));
        }
    }

    let mut js = String::from(RUNTIME);
    js.push('\n');
    js.push_str(TEXT_AS_STRING);
    js.push_str(CHARS_OF_TEXT);
    js.push_str(TEXT_OF_CHARS);
    js.push_str(RUNTIME_CODECS);
    js.push('\n');
    js.push_str(&shapes.js());
    js.push_str(DELAY_RUNTIME);
    js.push('\n');
    for &id in &used {
        js.push_str(&codegen.def(id).map_err(|e| {
            Diagnostic::from(e).with_label(g.def(id).span, "while generating JavaScript for this")
        })?);
    }
    let mut env = Vec::new();
    let main_js = codegen.expr(main, &mut env).map_err(Diagnostic::from)?;
    let _ = writeln!(
        js,
        "\n// `main()`, as `stitchwort run` runs it.\nconst MAIN = () => {main_js};"
    );
    js.push_str(
        &RUNNER
            .replace("@EXIT_IO@", &EXIT_IO.to_string())
            .replace("@EXIT_RESOURCE@", &EXIT_RESOURCE.to_string()),
    );
    Ok(Program {
        module: js,
        launcher: LAUNCHER
            .replace("@STACK_MB@", &STACK_MB.to_string())
            .replace("@EXIT_RESOURCE@", &EXIT_RESOURCE.to_string()),
    })
}

/// The JS for constructors the runner takes apart or builds: each one's tag,
/// and its runtime fields' keys.
struct Shapes {
    lines: Vec<(&'static str, String)>,
}

impl Shapes {
    fn new(g: &Globals) -> Result<Shapes, Diagnostic> {
        let data = |b: Builtin| -> Result<DataId, Diagnostic> {
            g.registry
                .data(b)
                .ok_or_else(|| internal(format!("the prelude doesn't declare `{}`", b.name())))
        };
        let ctor_of = |b: Builtin| -> Result<(DataId, usize), Diagnostic> {
            g.registry
                .ctor(b)
                .ok_or_else(|| internal(format!("the prelude doesn't declare `{}`", b.name())))
        };
        let mut lines = Vec::new();
        // A constructor's tag, and its runtime fields' keys, which must be
        // `fields` many.
        let mut ctor = |name: &'static str, d: DataId, c: usize, fields: &[&'static str]| {
            let data = g.data(d);
            let ctor = &data.ctors[c];
            if data.record {
                return Err(internal(format!("`{}` is a record", data.name)));
            }
            let keys: Vec<String> = (0..ctor.fields.len())
                .filter(|i| !ctor.field_erased[*i])
                .map(|i| field_key_at(g, d, c, i))
                .collect();
            if keys.len() != fields.len() {
                return Err(internal(format!(
                    "`{}` has {} runtime fields, not {}",
                    ctor.name,
                    keys.len(),
                    fields.len()
                )));
            }
            lines.push((name, js_string_literal(&ctor.name)));
            for (field, key) in fields.iter().zip(keys) {
                lines.push((field, js_string_literal(&key)));
            }
            Ok(())
        };
        let comp = data(Builtin::Comp)?;
        ctor("done", comp, 0, &["doneValue"])?;
        ctor("call", comp, 1, &["callOp", "callRest"])?;
        let plus = data(Builtin::Plus)?;
        ctor("left", plus, 0, &["leftOp"])?;
        ctor("right", plus, 1, &["rightOp"])?;
        ctor("recur", data(Builtin::Rec)?, 0, &["recurArg"])?;
        ctor("mkSigMap", data(Builtin::SigMap)?, 0, &["inject", "reply"])?;
        let io = data(Builtin::Io)?;
        ctor("print", io, ctor_of(Builtin::Print)?.1, &["printText"])?;
        ctor(
            "readLine",
            io,
            ctor_of(Builtin::ReadLine)?.1,
            &["readLineUnit"],
        )?;
        ctor(
            "readAll",
            io,
            ctor_of(Builtin::ReadAll)?.1,
            &["readAllUnit"],
        )?;
        let maybe = data(Builtin::Maybe)?;
        ctor("nothing", maybe, 0, &[])?;
        ctor("just", maybe, 1, &["justValue"])?;
        ctor("unit", data(Builtin::UnitType)?, 0, &[])?;
        Ok(Shapes { lines })
    }

    fn js(&self) -> String {
        let mut js = String::from(
            "// The constructors the runner takes apart and builds: tags and keys.\nconst SHAPE = {\n",
        );
        for (name, value) in &self.lines {
            let _ = writeln!(js, "  {name}: {value},");
        }
        js.push_str("};\n");
        js
    }
}

/// `Delay` values: one of its five constants applied to its runtime
/// arguments. Building one runs nothing.
const DELAY_RUNTIME: &str = r#"
// A partial computation (docs/proposals/partial.md §7.4): `now v`, `lift c`,
// `bindD d k`, `mapSig m d` or `pfix f x`. Only the runner looks inside.
const D_NOW = 0, D_LIFT = 1, D_BIND = 2, D_MAP = 3, D_PFIX = 4;
class StitchwortDelay {
  constructor(kind, a, b) {
    this.kind = kind;
    this.a = a;
    this.b = b;
  }
}

// `\y => Done y`, the continuation of an operation the elaborator writes:
// one value, so the runner can tell a request in tail position.
const DONE_K = (y) => ({ tag: SHAPE.done, [SHAPE.doneValue]: y });
"#;

/// The runner: `run_loop` and `perform` of `stitchwort_driver::run`, and the
/// machine of `stitchwort_core::step`.
const RUNNER: &str = r#"
// The runner (`stitchwort run --js`). It runs in a worker thread that
// `run.mjs` starts with a large stack.
import * as __fs from "node:fs";
import * as __wt from "node:worker_threads";

{
  const errorFile = __wt.workerData.errorFile;

  // Reading or writing failed: E-IO.
  class IoError extends Error {}

  const sleeper = new Int32Array(new SharedArrayBuffer(4));
  // A non-blocking descriptor with nothing ready yet: wait a little.
  const pause = () => Atomics.wait(sleeper, 0, 0, 2);

  // Standard output, buffered, and flushed before every read and at the end.
  let pending = [];
  let pendingLength = 0;
  const writeAll = (bytes) => {
    let offset = 0;
    while (offset < bytes.length) {
      try {
        offset += __fs.writeSync(1, bytes, offset, bytes.length - offset);
      } catch (e) {
        if (e.code === "EAGAIN") {
          pause();
          continue;
        }
        throw new IoError(`can't write standard output: ${e.message}`);
      }
    }
  };
  const flush = () => {
    if (pending.length === 0) return;
    const bytes = Buffer.from(pending.join(""), "utf8");
    pending = [];
    pendingLength = 0;
    writeAll(bytes);
  };
  const print = (text) => {
    pending.push(text, "\n");
    pendingLength += text.length + 1;
    if (pendingLength >= 1 << 16) flush();
  };

  // Standard input, read as it's needed. `input[position..]` is what hasn't
  // been taken yet, and has no LF before `scanned`.
  let input = Buffer.alloc(0);
  let position = 0;
  let scanned = 0;
  let ended = false;
  // Lines read so far, for errors.
  let lines = 0;
  const chunk = Buffer.allocUnsafe(1 << 16);
  // The next piece of input, or null at the end.
  const readChunk = () => {
    if (ended) return null;
    for (;;) {
      let n;
      try {
        n = __fs.readSync(0, chunk, 0, chunk.length, null);
      } catch (e) {
        if (e.code === "EAGAIN") {
          pause();
          continue;
        }
        if (e.code !== "EOF") throw new IoError(`can't read standard input: ${e.message}`);
        n = 0;
      }
      if (n === 0) {
        ended = true;
        return null;
      }
      return Buffer.from(chunk.subarray(0, n));
    }
  };
  const decoder = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true });
  const decode = (bytes) => {
    try {
      return decoder.decode(bytes);
    } catch {
      return null;
    }
  };
  // Where the first invalid UTF-8 sequence in `bytes` starts.
  const validUpTo = (bytes) => {
    let i = 0;
    while (i < bytes.length) {
      const c = bytes[i];
      let n, low = 0x80, high = 0xbf;
      if (c < 0x80) {
        i++;
        continue;
      } else if (c >= 0xc2 && c <= 0xdf) n = 1;
      else if (c >= 0xe0 && c <= 0xef) {
        n = 2;
        if (c === 0xe0) low = 0xa0;
        if (c === 0xed) high = 0x9f;
      } else if (c >= 0xf0 && c <= 0xf4) {
        n = 3;
        if (c === 0xf0) low = 0x90;
        if (c === 0xf4) high = 0x8f;
      } else return i;
      if (i + n >= bytes.length) return i;
      if (bytes[i + 1] < low || bytes[i + 1] > high) return i;
      for (let k = 2; k <= n; k++) if (bytes[i + k] < 0x80 || bytes[i + k] > 0xbf) return i;
      i += n + 1;
    }
    return i;
  };
  const invalid = (line) => new IoError(`line ${line} of standard input isn't valid UTF-8`);
  // The next line without its line ending (a trailing LF, and a CR just
  // before it), or null at the end.
  const readLine = () => {
    for (;;) {
      const lf = input.indexOf(10, scanned);
      if (lf >= 0) {
        const end = lf > position && input[lf - 1] === 13 ? lf - 1 : lf;
        const bytes = input.subarray(position, end);
        position = scanned = lf + 1;
        lines++;
        const line = decode(bytes);
        if (line === null) throw invalid(lines);
        return line;
      }
      scanned = input.length;
      const more = readChunk();
      if (more === null) break;
      input = Buffer.concat([input.subarray(position), more]);
      scanned -= position;
      position = 0;
    }
    if (position >= input.length) return null;
    const bytes = input.subarray(position);
    position = scanned = input.length;
    lines++;
    const line = decode(bytes);
    if (line === null) throw invalid(lines);
    return line;
  };
  // Everything that remains, exactly as it is.
  const readAll = () => {
    const parts = [input.subarray(position)];
    for (let more; (more = readChunk()) !== null; ) parts.push(more);
    const bytes = Buffer.concat(parts);
    input = Buffer.alloc(0);
    position = scanned = 0;
    const text = decode(bytes);
    if (text === null) {
      const valid = bytes.subarray(0, validUpTo(bytes));
      let before = 0;
      for (let i = valid.indexOf(10); i >= 0; i = valid.indexOf(10, i + 1)) before++;
      throw invalid(lines + before + 1);
    }
    let count = 0;
    for (let i = bytes.indexOf(10); i >= 0; i = bytes.indexOf(10, i + 1)) count++;
    lines += count + (text.length > 0 && !text.endsWith("\n") ? 1 : 0);
    return text;
  };

  // Performs an operation of `{IO}`, which is `Plus IO NoOp`: its reply.
  const perform = (o) => {
    if (o.tag !== SHAPE.left) throw new Error("internal error: an operation outside `IO`");
    const op = o[SHAPE.leftOp];
    switch (op.tag) {
      case SHAPE.print:
        print(op[SHAPE.printText]);
        return { tag: SHAPE.unit };
      case SHAPE.readLine: {
        flush();
        const line = readLine();
        return line === null
          ? { tag: SHAPE.nothing }
          : { tag: SHAPE.just, [SHAPE.justValue]: line };
      }
      case SHAPE.readAll:
        flush();
        return readAll();
      default:
        throw new Error("internal error: an unknown `IO` operation");
    }
  };

  // The machine of `stitchwort_core::step`: the focus, and a stack of
  // frames on the heap. Each `Recur` that reaches a `Tie` is a tick; with
  // no tick limit, the runner just goes on.
  const EVAL = 0, ENTER = 1, COMP = 2, RET = 3;
  const F_BIND = 0, F_MAP = 1, F_TIE = 2, F_AWAIT = 3;
  // Translates a reply back through the `Map` frames an operation passed
  // (`back`, innermost first, so they're undone outermost first).
  const translateBack = (frames, back, v) => {
    for (let i = back.length - 1; i >= 0; i--) {
      const [j, source] = back[i];
      v = frames[j].reply(source)(v);
    }
    return v;
  };
  const run = (delay) => {
    let mode = EVAL, a = delay, b;
    const frames = [];
    for (;;) {
      switch (mode) {
        case EVAL:
          switch (a.kind) {
            case D_NOW:
              mode = RET;
              a = a.a;
              break;
            case D_LIFT:
              mode = COMP;
              a = a.a;
              break;
            case D_BIND:
              frames.push({ k: F_BIND, f: a.b });
              a = a.a;
              break;
            case D_MAP:
              frames.push({ k: F_MAP, inject: a.a[SHAPE.inject], reply: a.a[SHAPE.reply] });
              a = a.b;
              break;
            case D_PFIX:
              // Building `pfix f x` ran nothing; stepping it enters the body.
              mode = ENTER;
              b = a.b;
              a = a.a;
              break;
            default:
              throw new Error("internal error: running something that isn't a `Delay`");
          }
          break;
        case ENTER:
          frames.push({ k: F_TIE, f: a });
          mode = EVAL;
          a = a(b);
          break;
        case COMP: {
          if (a.tag === SHAPE.done) {
            mode = RET;
            a = a[SHAPE.doneValue];
            break;
          }
          let op = a[SHAPE.callOp];
          const cont = a[SHAPE.callRest];
          // The operation leaves the focus, outwards through the frames.
          const back = [];
          let entered = false;
          for (let j = frames.length - 1; j >= 0; j--) {
            const frame = frames[j];
            if (frame.k === F_MAP) {
              const target = frame.inject(op);
              back.push([j, op]);
              op = target;
            } else if (frame.k === F_TIE) {
              if (op.tag !== SHAPE.left) {
                op = op[SHAPE.rightOp];
                continue;
              }
              // A recursion request: one tick.
              const request = op[SHAPE.leftOp][SHAPE.recurArg];
              const upper = frames.splice(j);
              const tail = upper.length === 1 && cont === DONE_K && back.length === 0;
              if (!tail) {
                frames.push({ k: F_AWAIT, cont, upper, back: back.map(([k, s]) => [k - j, s]) });
              }
              mode = ENTER;
              a = frame.f;
              b = request;
              entered = true;
              break;
            }
          }
          if (entered) break;
          // For the host.
          const reply = translateBack(frames, back, perform(op));
          a = cont(reply);
          break;
        }
        case RET: {
          const frame = frames.pop();
          if (frame === undefined) return a;
          switch (frame.k) {
            case F_BIND:
              mode = EVAL;
              a = frame.f(a);
              break;
            case F_AWAIT: {
              const v = translateBack(frame.upper, frame.back, a);
              for (const f of frame.upper) frames.push(f);
              mode = COMP;
              a = frame.cont(v);
              break;
            }
          }
          break;
        }
      }
    }
  };

  let code = 0;
  let message = "";
  try {
    run(MAIN());
    flush();
  } catch (e) {
    // What was printed before the error still appears. The first error is
    // the one reported.
    try {
      flush();
    } catch {}
    if (e instanceof IoError) {
      code = @EXIT_IO@;
      message = e.message;
    } else if (e instanceof RangeError || (e instanceof Error && e.name === "InternalError")) {
      code = @EXIT_RESOURCE@;
      message = e.message;
    } else {
      throw e;
    }
  }
  if (code !== 0) {
    __fs.writeFileSync(errorFile, message);
    process.exit(code);
  }
}
"#;

/// `run.mjs`: starts `program.mjs` in a worker thread with a large stack.
/// A worker's stack can be far larger than the main thread's, which is
/// limited by the operating system's.
const LAUNCHER: &str = r#"// Generated by stitchwort: runs program.mjs (`stitchwort run --js`).
import { Worker } from "node:worker_threads";
import { writeFileSync } from "node:fs";

const errorFile = process.argv[2];
const worker = new Worker(new URL("./program.mjs", import.meta.url), {
  workerData: { errorFile },
  resourceLimits: { stackSizeMb: @STACK_MB@ },
});
let failed = false;
worker.on("error", (e) => {
  failed = true;
  // Running out of stack while the module loads, or out of memory.
  if (e && (e.name === "RangeError" || e.code === "ERR_WORKER_OUT_OF_MEMORY")) {
    writeFileSync(errorFile, e.message);
    process.exitCode = @EXIT_RESOURCE@;
  } else {
    console.error(e);
    process.exitCode = 1;
  }
});
worker.on("exit", (code) => {
  if (!failed) process.exitCode = code;
});
"#;
