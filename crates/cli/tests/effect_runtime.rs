//! The JS effect runtime (docs/proposals/effect-runtime.md §9, D1162, stages
//! 4a and 4d): handler shapes over 1,000,000 elements on Node's default
//! stack, as a library user or the playground calls an export (D1163), and
//! counts of the runtime's work, which must grow linearly with the input.
//! Correctness against the reference evaluator is the `-- run:` lines of
//! `examples/extract/effect-runtime.sw`, `effect-handlers.sw` and
//! `effect-state.sw`, in the `extract` tests.
//!
//! Requires `node` on the PATH (the Nix dev shell provides it).

use std::path::Path;
use std::process::Command;

use stitchwort_cli::driver::Session;
use stitchwort_cli::render::render;
use stitchwort_core::Limits;
use stitchwort_js::Options;

/// The generated module for `examples/extract/effect-runtime.sw`, with the
/// runtime counting its work.
fn module() -> String {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/extract/effect-runtime.sw");
    let text = std::fs::read_to_string(&path).expect("readable example");
    let mut session = Session::new();
    if let Err(diagnostics) = session.load("effect-runtime.sw", &text) {
        let rendered: String = diagnostics
            .iter()
            .map(|d| render(&session.sources, d, false))
            .collect();
        panic!("effect-runtime.sw doesn't check:\n{rendered}");
    }
    let options = Options {
        effect_counters: true,
        ..Options::default()
    };
    stitchwort_js::generate_with(&session.elab.globals, Limits::default(), options)
        .expect("extraction succeeds")
        .js
}

/// Runs `script` with the module beside it as `module.mjs`, on Node's
/// default stack, and returns what it printed.
fn run_script(name: &str, script: &str) -> String {
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-effect-runtime-{}-{name}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    std::fs::write(dir.join("module.mjs"), module()).expect("write module");
    std::fs::write(dir.join("test.mjs"), format!("{PRELUDE}{script}")).expect("write script");
    let result = Command::new("node")
        .arg("test.mjs")
        .current_dir(&dir)
        .output()
        .expect("run `node` (is it on the PATH? `nix develop` provides it)");
    let stdout = String::from_utf8_lossy(&result.stdout).into_owned();
    assert!(
        result.status.success(),
        "node failed:\n{}\n{stdout}",
        String::from_utf8_lossy(&result.stderr),
    );
    let _ = std::fs::remove_dir_all(&dir);
    stdout
}

const PRELUDE: &str = r#"
import * as m from "./module.mjs";
import assert from "node:assert/strict";

const list = (n) => Array.from({ length: n }, (_, i) => BigInt(i));
const counts = () => globalThis.__stitchwortEffectCounts;
const reset = () => {
  const c = counts();
  for (const key of Object.keys(c)) c[key] = 0;
};
const ok = (result) => {
  assert.equal(result.$tag, "Ok", `expected Ok, got ${JSON.stringify(result.$tag)}`);
  return result.value;
};
// Each shape: the call, and a check of its result for a list of `n`.
const plus = (k) => (xs) => {
  assert.equal(xs.length, n);
  for (let i = 0; i < xs.length; i += 9973) assert.equal(xs[i], BigInt(i) + k);
  assert.equal(xs[n - 1], BigInt(n - 1) + k);
};
let n = 0;
// Each element numbered twice its index (`x + next()`).
const twice = (ys) => {
  assert.equal(ys.length, n);
  for (let i = 0; i < n; i += 9973) assert.equal(ys[i], 2n * BigInt(i));
  assert.equal(ys[n - 1], 2n * BigInt(n - 1));
};
const shapes = {
  checked: [(xs) => ok(m.checked(xs)), plus(1n)],
  asked: [(xs) => m.asked(xs), plus(7n)],
  askedChecked: [(xs) => ok(m.askedChecked(xs)), plus(7n)],
  askedIn: [(xs) => ok(m.askedIn(xs)), plus(7n)],
  emittedIn: [(xs) => ok(m.emittedIn(xs)), plus(0n)],
  searchedIn: [(xs) => ok(m.searchedIn(xs)), (results) => {
    assert.equal(results.length, 1);
    plus(0n)(results[0]);
  }],
  countedIn: [(xs) => ok(m.countedIn(xs)), twice],
  forwarded10: [(xs) => m.forwarded(10n, xs), plus(7n)],
  // State-passing handlers at the empty row, run as a loop (stage 4d).
  counted: [(xs) => m.counted(xs), twice],
  countedChecked: [(xs) => ok(m.countedChecked(BigInt(n), xs)), twice],
  countedOpen: [(xs) => m.countedOpen(xs), twice],
  logged: [(xs) => m.logged(xs), plus(0n)],
};
const stateShapes = new Set(["counted", "countedChecked", "countedOpen", "logged"]);
"#;

/// Every shape that should be stack-safe in JS under stage 4a runs on Node's
/// default stack at 1,000,000 elements, with the right answer. `failsLast`
/// performs its one operation at the very end, so the whole list is pending.
#[test]
fn every_shape_runs_at_a_million_elements_on_the_default_stack() {
    let out = run_script(
        "million",
        r#"
n = 1_000_000;
const xs = list(n);
for (const [name, [call, check]] of Object.entries(shapes)) {
  const start = performance.now();
  check(call(xs));
  console.log(`${name}\t${(performance.now() - start).toFixed(0)} ms`);
}
const failed = m.failsLast(BigInt(n), xs);
assert.deepEqual(failed, { $tag: "Err", error: "last" });
console.log("done");
"#,
    );
    println!("{out}");
    assert!(out.ends_with("done\n"), "{out}");
}

/// A closed signature map is built once, at its first use, and kept in a
/// module variable (stage 4f, stitchwort_rt::hoist): `searchedIn`'s
/// `Each.each` is wrapped in a `translate` from `{Each}` to `{Each, Fail}`
/// for every element, and its map is `sigmap$…`, not a call of `sigCase`
/// on every element.
#[test]
fn closed_signature_maps_are_built_once() {
    let js = module();
    let def = js
        .lines()
        .find(|l| l.starts_with("const $Main$dsearchedIn = "))
        .expect("searchedIn is generated");
    let at = def.find("$Std$dEffect$dsigCase(").expect("its map");
    assert!(def[..at].ends_with(" ??= "), "{def}");
    assert!(def[..at].contains("(sigmap$"), "{def}");
    assert!(
        js.lines().any(|l| l.starts_with("var sigmap$0")),
        "the maps' variables are declared"
    );
}

/// A known definition called with all its runtime arguments is one call,
/// `f(a, b)`, not one call per argument (D1173): `List.map`, `bindIn` and
/// `doneIn` take theirs together, and so do the effect runtime's `bind` and
/// `foldComp`.
#[test]
fn known_calls_pass_their_arguments_together() {
    let js = module();
    let def = |name: &str| {
        js.lines()
            .find(|l| l.starts_with(&format!("const {name} = ")))
            .unwrap_or_else(|| panic!("{name} is generated"))
            .to_string()
    };
    assert!(def("$Std$dList$dmap").ends_with(" = (v1, v3, v4) => {"));
    assert!(def("$Std$dEffect$dbindIn").ends_with(" = (v2, v3, v4) => {"));
    assert_eq!(
        def("$Std$dEffect$dfoldComp"),
        "const $Std$dEffect$dfoldComp = (done, call, c) => effFold(done, call, c, null);"
    );
    assert!(js.contains("$Std$dEffect$dbindIn(v1, $Std$dList$dmap(v1, v3, v6), "));
    for curried in [
        "$Std$dList$dmap(v1)(",
        "$Std$dEffect$dbindIn(v1)(",
        "$Std$dEffect$dbind(v3)(",
    ] {
        assert!(!js.contains(curried), "{curried}");
    }
}

/// The runtime's work grows linearly: run-loop steps, pushes and pops of
/// pending continuations, and resumptions per element are the same at
/// 1,000, 10,000 and 100,000 elements (so nothing rebuilds a pending list or
/// rescans it), and an operation is routed through each handler and
/// `translate` it crosses once, however long the pending list is.
#[test]
fn the_work_per_element_is_constant() {
    let out = run_script(
        "linear",
        r#"
const sizes = [1_000, 10_000, 100_000];
for (const [name, [call, check]] of Object.entries(shapes)) {
  const per = [];
  for (const size of sizes) {
    n = size;
    const xs = list(n);
    reset();
    check(call(xs));
    const c = { ...counts() };
    if (stateShapes.has(name)) {
      // Every operation is a jump of the handler's loop.
      assert.equal(c.jumps, n, `${name}: jumps at ${n}`);
    } else {
      assert.equal(c.jumps, 0, `${name}: jumps at ${n}`);
    }
    per.push(Object.fromEntries(Object.entries(c).map(([k, v]) => [k, v / n])));
  }
  for (const key of Object.keys(per[0])) {
    const [small, , large] = per.map((p) => p[key]);
    // Linear: the work per element doesn't grow (a fixed amount of work per
    // call shows up as a little more per element at 1,000).
    assert.ok(large <= small + 0.01, `${name}: ${key} per element grew from ${small} to ${large}`);
    // And small: a few steps per `bind`, a few `bind`s per element.
    // (`forwarded10`'s operations each cross eleven handlers.)
    const crossed = name === "forwarded10" ? 11 : 1;
    assert.ok(large <= 40 * crossed, `${name}: ${key} per element is ${large}`);
  }
  // Every pending continuation pushed is popped.
  assert.equal(counts().pushes, counts().pops, `${name}: pushes and pops differ`);
  console.log(name, JSON.stringify(per[2]));
}

// Routing: at most a constant per operation and handler crossed. `ask` crosses
// `depth` handlers of another ability (each with a `translate`) on its way to
// the reader, whatever the length of the list.
for (const depth of [1, 10, 100]) {
  const per = [];
  for (const size of [1_000, 10_000]) {
    n = size;
    reset();
    plus(7n)(m.forwarded(BigInt(depth), list(n)));
    per.push(counts().routes / (n * (depth + 1)));
  }
  assert.ok(per[1] <= per[0] + 0.01, `forwarded ${depth}: routes grew from ${per[0]} to ${per[1]}`);
  assert.ok(per[1] <= 3, `forwarded ${depth}: ${per[1]} routes per operation and handler`);
  console.log(`forwarded ${depth}: ${per[1]} routes per operation and handler`);
}
console.log("done");
"#,
    );
    println!("{out}");
    assert!(out.ends_with("done\n"), "{out}");
}

/// The stage's documented limit (docs/proposals/effect-runtime.md §9.1.7):
/// a handler at the empty row whose clause uses the resumption's result
/// inside pure code (`Cons v (k ())`, `Each.collect`) is a pure non-tail
/// recursion, one level per operation, and keeps JS's stack limit. They
/// work on short lists and fail cleanly, with the module's resource error,
/// on long ones. If one of them starts to pass, the limit has moved: update
/// the note and this test.
#[test]
fn empty_row_non_tail_handlers_keep_the_stack_limit() {
    let out = run_script(
        "limit",
        r#"
// About 1,000 to 2,000 operations fit on Node's default stack, as before stage 4a.
const small = list(500);
assert.equal(m.emitted(small).length, 500);
assert.equal(m.searched(small).length, 1);
const large = list(1_000_000);
for (const name of ["emitted", "searched"]) {
  assert.throws(() => m[name](large), (e) => e instanceof m.StitchwortResourceError, name);
}
console.log("done");
"#,
    );
    println!("{out}");
    assert!(out.ends_with("done\n"), "{out}");
}

/// `examples/accept/partial-forwarding.sw` as `run --js` runs it, with the
/// runner counting its routing (`generate_program_with`): a non-tail partial
/// recursion as deep as the first input line, whose every level prints
/// through handlers that forward `IO`.
fn partial_forwarding_program() -> stitchwort_js::run::Program {
    let name = "partial-forwarding.sw";
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/accept")
        .join(name);
    let text = std::fs::read_to_string(&path).expect("readable example");
    let mut session = Session::new();
    if let Err(diagnostics) = session.load(name, &text) {
        let rendered: String = diagnostics
            .iter()
            .map(|d| render(&session.sources, d, false))
            .collect();
        panic!("{name} doesn't check:\n{rendered}");
    }
    let main = session.main().expect("a `main`");
    let options = Options {
        effect_counters: true,
        ..Options::default()
    };
    stitchwort_js::run::generate_program_with(
        &session.elab.globals,
        session.elab.limits,
        main.term(),
        options,
    )
    .expect("generation succeeds")
}

/// What `partial-forwarding.sw` prints last for `depth`: each level adds 1
/// and the number of Collatz steps from `n % 8 + 1` to 1.
fn partial_forwarding_total(depth: u64) -> u64 {
    let collatz = |mut n: u64| {
        let mut steps = 0;
        while n != 1 {
            n = if n.is_multiple_of(2) {
                n / 2
            } else {
                3 * n + 1
            };
            steps += 1;
        }
        steps
    };
    (1..=depth).map(|n| 1 + collatz(n % 8 + 1)).sum()
}

/// The routing counts of a `run --js` run: operations, frames routing
/// looked at, and frames below the focus at each operation, summed.
struct RouteCounts {
    operations: f64,
    visited: f64,
    below: f64,
}

/// Runs `program` at `depth` under Node, as `run --js` does (in a worker
/// with a large stack), checks what it printed, and returns its counts.
fn run_partial_forwarding(program: &stitchwort_js::run::Program, depth: u64) -> RouteCounts {
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-partial-forwarding-{}-{depth}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    std::fs::write(dir.join("program.mjs"), &program.module).expect("write program");
    std::fs::write(dir.join("run.mjs"), &program.launcher).expect("write launcher");
    std::fs::write(dir.join("input.txt"), format!("{depth}\n")).expect("write input");
    let result = Command::new("node")
        .args(["run.mjs", "error.txt"])
        .current_dir(&dir)
        .stdin(std::fs::File::open(dir.join("input.txt")).expect("input"))
        .output()
        .expect("run `node` (is it on the PATH? `nix develop` provides it)");
    let stdout = String::from_utf8_lossy(&result.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&result.stderr).into_owned();
    assert!(result.status.success(), "node failed at {depth}:\n{stderr}");
    let _ = std::fs::remove_dir_all(&dir);
    let mut lines = stdout.lines();
    for n in (1..=depth).rev() {
        assert_eq!(lines.next(), Some(n.to_string().as_str()), "at {depth}");
    }
    let total = format!("total {}", partial_forwarding_total(depth));
    assert_eq!(lines.next(), Some(total.as_str()), "at {depth}");
    assert_eq!(lines.next(), None, "at {depth}");
    let counts = stderr
        .lines()
        .find_map(|l| l.strip_prefix("stitchwort-route-counts "))
        .unwrap_or_else(|| panic!("no counts at {depth}:\n{stderr}"));
    let field = |key: &str| {
        let start = counts.find(&format!("\"{key}\":")).expect("the key") + key.len() + 3;
        let rest = &counts[start..];
        let end = rest.find([',', '}']).expect("the value ends");
        rest[..end].parse::<f64>().expect("a number")
    };
    RouteCounts {
        operations: field("operations"),
        visited: field("visited"),
        below: field("below"),
    }
}

/// The `run --js` runner routes an operation by its index of `Map` and `Tie`
/// frames, never looking at the ordinary frames between them (§9.1.6, stage
/// 4c), as the native runner does: in `partial-forwarding.sw` every `print`
/// leaves the focus with one waiting frame per level below it, so the
/// frames below the focus per operation grow with the depth, while the
/// frames routing looks at per operation stay the same, a few.
#[test]
fn run_js_routing_work_is_independent_of_control_depth() {
    let program = partial_forwarding_program();
    let mut per = Vec::new();
    for depth in [1_000, 10_000, 100_000] {
        let c = run_partial_forwarding(&program, depth);
        let (visited, below) = (c.visited / c.operations, c.below / c.operations);
        println!("depth {depth}: per operation, {visited} visited and {below} below");
        assert!(below >= depth as f64 / 8.0, "depth {depth}: {below} below");
        per.push(visited);
    }
    assert!(
        per[2] <= per[0] + 0.01,
        "visited per operation grew: {per:?}"
    );
    assert!(per[2] <= 4.0, "visited per operation: {per:?}");
}

/// `Partial` mixed with other forwarded abilities, a million levels deep,
/// under `run --js`.
#[test]
fn run_js_partial_with_forwarded_abilities_runs_a_million_levels_deep() {
    let program = partial_forwarding_program();
    let c = run_partial_forwarding(&program, 1_000_000);
    println!("{} operations, {} visited", c.operations, c.visited);
}
