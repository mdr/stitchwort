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
//! `() -> {IO, Partial} ()`, or `() -> {IO, Fail, Partial} ()` for a `main`
//! that may fail, so a total or pure `main` arrives lifted, as in the Rust
//! runner. The runner performs `Fail.stop` itself, as it performs `print`
//! (docs/proposals/partial-stage-2.md). Unlike `build --js`, a `Delay` isn't erased to a token
//! here (docs/proposals/partial.md §7.6): its constants build
//! `StitchwortDelay` objects, and the runner steps them with the machine of
//! `stitchwort_core::step`, frame for frame. JS has no tick limit and no
//! evaluation budget: a loop just loops, as with `stitchwort run`.
//!
//! The runner reports how a run failed by its exit code, with the message
//! in a file the CLI names: [`EXIT_RESOURCE`] when the program ran out of
//! the engine's stack or memory (or made a number or string too large for
//! it), [`EXIT_IO`] when reading or writing failed, [`EXIT_FAIL`] when `main`
//! failed with an unhandled `Fail`.

use std::fmt::Write;

use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, Globals, Limits, Term};
use stitchwort_syntax::Diagnostic;

use super::{
    CHARS_OF_TEXT, Convention, Gen, Options, RUNTIME, RUNTIME_CODECS, TEXT_AS_STRING,
    TEXT_OF_CHARS, erasable, field_key_at, js_string_literal,
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
/// The runner's exit code when `main` failed with `Fail` and nothing handled
/// it: the message is in the error file (docs/proposals/errors.md §3.5).
pub const EXIT_FAIL: i32 = 72;

/// The worker thread's stack, in megabytes. It's reserved, not used: memory
/// is taken only as deep as the program recurses. 2 GB is about ten million
/// frames of a simple recursion.
pub const STACK_MB: u32 = 2048;

/// The JS name of the continuation `y => Done y` (see
/// `stitchwort_rt::erasure::is_done_continuation`).
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
        // Never emitted: `run --js` refuses `foldD` once it knows what
        // `main` uses (lane C of docs/proposals/partial-handlers.md), but
        // the code generator reads its shape before that.
        Primitive::FoldD => "(done) => (call) => (d) => { throw new Error('foldD'); }",
        Primitive::Delay => unreachable!("`Delay` is a type, so it's erased"),
    }
}

/// How many runtime arguments each constant takes in [`primitive_js`].
fn runtime_arity(prim: Primitive) -> usize {
    match prim {
        Primitive::Now | Primitive::Lift => 1,
        Primitive::BindD | Primitive::MapSig | Primitive::Pfix => 2,
        Primitive::FoldD => 3,
        Primitive::Delay => 0,
    }
}

fn internal(message: String) -> Diagnostic {
    Diagnostic::error("E-EXPORT", format!("internal error: {message}"))
}

/// Generates the program that runs `main`: the closed term of type
/// `{IO, Partial} ()` or `{IO, Fail, Partial} ()` that `stitchwort run` runs
/// (`Main`'s term in the driver). Constructors are tagged by name here, so
/// the runner tells a `Fail` operation from an `IO` one by its tag, in
/// either row.
pub fn generate_program(g: &Globals, limits: Limits, main: &Term) -> Result<Program, Diagnostic> {
    generate_program_with(g, limits, main, Options::default())
}

/// [`generate_program`] with `options`. With `effect_counters`, the runner
/// also counts the operations it routes, the frames routing looks at, and
/// the frames below the focus at each operation (`operations`, `visited`
/// and `below`, beside the effect runtime's counts; as
/// `stitchwort_rt::RouteCounts`), and prints them to standard error at the
/// end as a line `stitchwort-route-counts {"operations":…,…}`, for tests.
pub fn generate_program_with(
    g: &Globals,
    limits: Limits,
    main: &Term,
    options: Options,
) -> Result<Program, Diagnostic> {
    let _op = g.budget.operation(Limits::stack_only(limits.stack));
    erasable(g)?;
    let counters = options.effect_counters;
    let mut codegen = Gen::new(g, options)?;
    codegen.run_delay = true;
    if codegen.text.is_none() {
        return Err(internal(
            "the prelude's `Text` doesn't have the representation `run --js` expects".into(),
        ));
    }
    let shapes = Shapes::new(g)?;

    let used = codegen.set_reach([], &[main], false)?;
    for &id in &used {
        let info = codegen.try_info(id)?;
        let def = g.def(id);
        if let Some(prim) = g.builtins.primitive(id) {
            // A handler around partial code (docs/proposals/partial-handlers.md)
            // runs only on the reference runner so far; lane C of that note.
            if prim == Primitive::FoldD {
                return Err(Diagnostic::error(
                    "E-RUNTIME",
                    "a handler around partial code isn't supported on this runner yet",
                )
                .with_note("run it with `stitchwort run --reference`"));
            }
            let runtime = info.mask.iter().filter(|erased| !**erased).count();
            if info.convention != Convention::Erased && runtime != runtime_arity(prim) {
                return Err(internal(format!(
                    "`{}` takes {runtime} runtime arguments, not {}",
                    def.name,
                    runtime_arity(prim)
                )));
            }
        } else if def.body().is_none() && !info.result_erased && !codegen.is_native(id) {
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
    if codegen.float.is_some() {
        js.push_str(crate::FLOAT_BITS);
    }
    js.push_str(TEXT_AS_STRING);
    js.push_str(CHARS_OF_TEXT);
    js.push_str(TEXT_OF_CHARS);
    js.push_str(RUNTIME_CODECS);
    js.push('\n');
    js.push_str(&shapes.js());
    js.push_str(DELAY_RUNTIME);
    // The runner takes computations apart with the effect runtime's loop.
    let effect = codegen
        .effect
        .as_ref()
        .ok_or_else(|| internal("the core's effect machinery isn't loaded".into()))?;
    js.push_str(effect.runtime());
    js.push('\n');
    for id in crate::dependency_order(&codegen, &used) {
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
    js.push_str(&codegen.hoisted_vars());
    js.push_str(
        &RUNNER
            .replace("@EXIT_IO@", &EXIT_IO.to_string())
            .replace("@EXIT_FAIL@", &EXIT_FAIL.to_string())
            .replace("@EXIT_RESOURCE@", &EXIT_RESOURCE.to_string())
            .replace(
                "@COUNT_OPERATION@",
                if counters {
                    "effCount.operations++;\n          effCount.below += frames.length;\n          "
                } else {
                    ""
                },
            )
            .replace(
                "@COUNT_VISIT@",
                if counters {
                    "effCount.visited++;\n            "
                } else {
                    ""
                },
            )
            .replace(
                "@REPORT_COUNTS@",
                if counters {
                    "__fs.writeSync(2, `stitchwort-route-counts ${JSON.stringify({ operations: effCount.operations, visited: effCount.visited, below: effCount.below })}\\n`);\n  "
                } else {
                    ""
                },
            ),
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
        ctor(
            "console",
            io,
            ctor_of(Builtin::IoConsole)?.1,
            &["consoleUnit"],
        )?;
        ctor(
            "keysMode",
            io,
            ctor_of(Builtin::KeysMode)?.1,
            &["keysModeOn"],
        )?;
        ctor(
            "readBytes",
            io,
            ctor_of(Builtin::ReadBytes)?.1,
            &["readBytesUnit"],
        )?;
        ctor("write", io, ctor_of(Builtin::IoWrite)?.1, &["writeText"])?;
        let bool_ = data(Builtin::Bool)?;
        ctor("false_", bool_, ctor_of(Builtin::False)?.1, &[])?;
        ctor("true_", bool_, ctor_of(Builtin::True)?.1, &[])?;
        let list = data(Builtin::List)?;
        ctor("nil", list, ctor_of(Builtin::Nil)?.1, &[])?;
        ctor("cons", list, ctor_of(Builtin::Cons)?.1, &["head", "tail"])?;
        ctor(
            "randomSeed",
            io,
            ctor_of(Builtin::RandomSeed)?.1,
            &["randomSeedUnit"],
        )?;
        // `Fail`'s one operation, once its library file has loaded: a `main`
        // that may fail loads it.
        if let Some(fail) = g.registry.loaded_data(Builtin::Fail) {
            ctor("stop", fail, 0, &["stopMessage"])?;
        }
        let maybe = data(Builtin::Option)?;
        ctor("nothing", maybe, 0, &[])?;
        ctor("just", maybe, 1, &["someValue"])?;
        ctor("unit", data(Builtin::UnitType)?, 0, &[])?;
        // `Console`, a record: no tag, its fields' keys.
        let console = data(Builtin::Console)?;
        let fields = &g.data(console).ctors[0].fields;
        let names = [
            "consoleInput",
            "consoleOutput",
            "consoleColumns",
            "consoleRows",
        ];
        if fields.len() != names.len() {
            return Err(internal(format!(
                "`Console` has {} fields, not {}",
                fields.len(),
                names.len()
            )));
        }
        for (i, name) in names.into_iter().enumerate() {
            lines.push((name, js_string_literal(&field_key_at(g, console, 0, i))));
        }
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

// `y => Done y`, the continuation of an operation the elaborator writes:
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
  // `main` failed with `Fail.stop msg`, and nothing handled it.
  class FailError extends Error {}

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
  // The bytes of one read, for `readBytes`: what's buffered, or one read if
  // nothing is; null at the end.
  const readBytes = () => {
    let bytes = input.subarray(position);
    if (bytes.length === 0) bytes = readChunk();
    input = Buffer.alloc(0);
    position = scanned = 0;
    if (bytes === null) return null;
    for (let i = bytes.indexOf(10); i >= 0; i = bytes.indexOf(10, i + 1)) lines++;
    return bytes;
  };
  // A list of the bytes, as `Nat`s.
  const byteList = (bytes) => {
    let list = { tag: SHAPE.nil };
    for (let i = bytes.length - 1; i >= 0; i--) {
      list = { tag: SHAPE.cons, [SHAPE.head]: BigInt(bytes[i]), [SHAPE.tail]: list };
    }
    return list;
  };

  // Performs an operation of `{IO}`, which is `Plus IO NoOp`, or of
  // `{Fail, IO}`, which is `Plus Fail (Plus IO NoOp)`: its reply.
  // `Fail.stop msg` stops the run; it returns `Empty`, so there's nothing to
  // resume with.
  const perform = (o) => {
    while (o.tag === SHAPE.right) o = o[SHAPE.rightOp];
    if (o.tag !== SHAPE.left) {
      throw new Error("internal error: an operation outside `IO` and `Fail`");
    }
    const op = o[SHAPE.leftOp];
    switch (op.tag) {
      case SHAPE.stop:
        throw new FailError(op[SHAPE.stopMessage]);
      case SHAPE.print:
        print(op[SHAPE.printText]);
        return { tag: SHAPE.unit };
      case SHAPE.readLine: {
        flush();
        const line = readLine();
        return line === null
          ? { tag: SHAPE.nothing }
          : { tag: SHAPE.just, [SHAPE.someValue]: line };
      }
      case SHAPE.readAll:
        flush();
        return readAll();
      // Terminal control (docs/proposals/terminal-io.md §4.2), in the form
      // for pipes for now: `console` says neither side is a terminal, so a
      // program reads and draws as it would through pipes, and keys mode
      // changes nothing, so `print`, `readLine` and `readAll` have no mode to
      // leave. Raw mode through `stty` comes later (§4.7).
      case SHAPE.console:
        return {
          [SHAPE.consoleInput]: { tag: SHAPE.false_ },
          [SHAPE.consoleOutput]: { tag: SHAPE.false_ },
          [SHAPE.consoleColumns]: 0n,
          [SHAPE.consoleRows]: 0n,
        };
      case SHAPE.keysMode:
        return { tag: SHAPE.unit };
      case SHAPE.readBytes: {
        flush();
        const bytes = readBytes();
        return bytes === null
          ? { tag: SHAPE.nothing }
          : { tag: SHAPE.just, [SHAPE.someValue]: byteList(bytes) };
      }
      case SHAPE.write:
        pending.push(op[SHAPE.writeText]);
        flush();
        return { tag: SHAPE.unit };
      case SHAPE.randomSeed: {
        // Eight random bytes as a `Nat`, a bigint: the OS's entropy.
        const words = new BigUint64Array(1);
        globalThis.crypto.getRandomValues(words);
        return words[0];
      }
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
  // In `COMP` mode, `a` is a computation and `pending` the continuations
  // waiting for its result: the effect runtime's list, kept apart from the
  // machine's frames, so routing an operation looks only at `Map` and `Tie`
  // frames, never at a computation's continuations one by one
  // (docs/proposals/effect-runtime.md §9.1). `marks` holds the positions of
  // the `Map` and `Tie` frames in `frames`, bottom first, and routing walks
  // only those, never the `Bind` and `Await` frames between them (§9.1.6): a
  // deep non-tail recursion leaves an `Await` per level.
  const run = (delay) => {
    let mode = EVAL, a = delay, b, pending = null;
    const frames = [];
    const marks = [];
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
              pending = null;
              break;
            case D_BIND:
              frames.push({ k: F_BIND, f: a.b });
              a = a.a;
              break;
            case D_MAP:
              marks.push(frames.length);
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
          marks.push(frames.length);
          frames.push({ k: F_TIE, f: a });
          mode = EVAL;
          a = a(b);
          break;
        case COMP: {
          a = effRun(a, pending);
          if (a.tag === SHAPE.done) {
            mode = RET;
            a = a[SHAPE.doneValue];
            break;
          }
          let op = a[SHAPE.callOp];
          const cont = a[SHAPE.callRest];
          const after = effPending;
          // The operation leaves the focus, outwards through the marked
          // frames.
          const back = [];
          let entered = false;
          @COUNT_OPERATION@for (let p = marks.length - 1; p >= 0; p--) {
            const j = marks[p];
            const frame = frames[j];
            @COUNT_VISIT@if (frame.k === F_MAP) {
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
              const upperMarks = marks.splice(p);
              const tail =
                upper.length === 1 && cont === DONE_K && after === null && back.length === 0;
              if (!tail) {
                frames.push({
                  k: F_AWAIT,
                  cont,
                  after,
                  upper,
                  marks: upperMarks.map((k) => k - j),
                  back: back.map(([k, s]) => [k - j, s]),
                });
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
          pending = after;
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
            case F_MAP:
            case F_TIE:
              marks.pop();
              break;
            case F_AWAIT: {
              const v = translateBack(frame.upper, frame.back, a);
              const base = frames.length;
              for (const f of frame.upper) frames.push(f);
              for (const k of frame.marks) marks.push(k + base);
              mode = COMP;
              a = frame.cont(v);
              pending = frame.after;
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
    if (e instanceof FailError) {
      code = @EXIT_FAIL@;
      message = e.message;
    } else if (e instanceof IoError) {
      code = @EXIT_IO@;
      message = e.message;
    } else if (e instanceof RangeError || (e instanceof Error && e.name === "InternalError")) {
      code = @EXIT_RESOURCE@;
      message = e.message;
    } else {
      throw e;
    }
  }
  @REPORT_COUNTS@if (code !== 0) {
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
