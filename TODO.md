# To do

The working list for Stitchwort. Reorder, edit or delete freely: the order of
**Next** is the order work happens in. Design detail lives in `DESIGN.md` and
`docs/proposals/`; this file only tracks what's to do and why.

How it's kept:
- **Now** is what's in progress (ideally one thing).
- When something is finished, it moves to **Recently done** with its commit,
  and the oldest entries there are dropped (git log has the full history).
- New findings go under **Later** or **Known issues**, not straight into
  **Next**, unless they block what's in progress.

## Now

Work runs in lanes, each in its own git worktree and branch, merged into
`main` one at a time (with `nix flake check` after each). Only `main` edits
this file.

The main session orchestrates: it chooses lanes, hands each to a background
agent, then reviews, merges and updates this file.

Round 2:
- ~~Stack-safe step 4~~ (lane `depth-guards`): merged as `d166039`.
- ~~Text step 5~~ (lane `run`): merged as `65f91ce`.
- ~~Text step 6~~ (lane `playground-run`): merged as `f35f1a7`.
- ~~Syntax colouring in the playground~~ (lane `syntax-colour`): merged as
  `ccebba3`.
- **Text step 3** (lane `js-text`): item 1 of **Next**, in progress.

## Next

1. **Text, step 3** ([proposal](docs/proposals/text-and-io.md)): JS encoders
   and decoders for `Text` and `Char`, the boundary tests (surrogates, NUL,
   noncharacters, both round-trip laws), and differential tests including the
   cross-runtime counterexamples. Decide how generated JS copes with long
   texts, since JS engines don't eliminate tail calls.

## Later

- **Compact text** (text step 7): in generated JS first, then possibly in the
  checking evaluator, with differential tests against the plain-list version.
- **`==` operands are computed at check time.** `f x == y` puts `f x = y` in
  a type, so checking computes `f x`. Needs lazily evaluated values, or a
  translation of `==` that keeps its operands out of types.
- **Elaborating a chain is quadratic:** `expr.span()` and `may_perform` walk
  the whole subexpression at every level.
- **The WebAssembly guard size:** 128 KiB gives the playground about 25
  levels of nesting and list literals of about 200 elements. 256 KiB would
  roughly double that, with a 2× margin in Node. Separately, the parser's
  stack use per level could be cut (e.g. by boxing the `Diagnostic` in its
  `Result`).
- **Long list and text literals** stop at about 1,800 elements in a 2 MiB
  thread (about 75,000 in the CLI); waits on compact literals or checking
  literals without recursion.
- **The printer prints a function type's domain twice** in some branches,
  which may grow exponentially with nested domains (not measured).
- **Mutation testing** (in small sharded runs): the machine (`value.rs`),
  `budget.rs`, `native.rs` (167 mutants, never done).
- **Recorded benchmarks** with a regression threshold: the example suite,
  `lengths 400 3000`, text split/join on 10⁴ characters, generated rows.
- **Prove** `textToNat (natToText n) = Just n` (needs lemmas about `/` and
  `%`; tested only, for now).
- **`stitchwort run` out of resources** is tested only in the driver, not
  through the command (with the command's limits it needs about 1.5 GB).
  Perhaps a hidden option or environment variable to lower the limits.
- **Exit codes for `stitchwort run`:** every failure is 1. Decide whether
  "didn't check" and "failed while running" should differ.
- **`IO` operations that return `Result`** for recoverable errors (deferred
  by the text-and-IO proposal).
- **Stream a run's output** to the playground (the worker could post each
  flush), so a stopped or timed-out run still shows what it printed.
- **An automated browser test of the playground** (headless Chrome over the
  DevTools protocol, as done by hand for step 6): the tabs, Run, Stop, crash
  recovery, and the in-page fallback when workers can't start.
- **A budget on operations per playground run**, alongside the 15 s limit (a
  program reading past the end of its input many times is caught only by
  the timeout).
- **Playground editor quirks** (from before syntax colouring): dragging to
  resize the editor does nothing, and Tab's inserted spaces (via
  `setRangeText`) can't be undone and break Ctrl+Z for earlier typing.
  Colouring is checked only in headless Chrome (not Firefox or Safari, not
  with physical typing, not at phone width).
- **`Partial`** ([proposal](docs/proposals/partial.md)): until it's settled, an
  infinite `Comp` is unsound.
- **Lacks constraints on row variables** aren't enforced (only reachable with
  a hand-written `Sig`).
- **Inferring a bare lambda's type** needs an annotation, e.g.
  `runState ((\n -> n) : Nat -> {Choose} Nat) …`.
- **Forward references and mutual recursion.**
- **Records** (milestone 8).
- **Performance of effectful code** (deep handler trees) hasn't been measured.
- **Namespaces or modules.** Prelude names can't be redefined, so text
  operations are prefixed (`textLength`, `textSplit`) and every new prelude
  name risks clashing with user code.
- **Number patterns: the 256 cap, and the cost below it** (low priority).
  A number pattern `f n = …` is compiled as `n` nested `Succ`s, so patterns
  above 256 are refused (`E-UNSUPPORTED`), e.g. HTTP status codes. Below the
  cap, checking time grows faster than quadratically with the largest number
  (release CLI: `f 100` 0.16 s, `f 200` 1.0 s, `f 256` 2.0 s and 230 MB; a
  table `f 0` … `f 255` is the same 2.0 s). A sample of `f 256` puts ~75% of
  the time in checking the case tree (`check_tree`) and ~25% in the kernel's
  `check_case`, not in building the tree. Hand-written deep constructor
  patterns (the depth-guards lane: 400 deep, 17 s, 1.4 GB) are unrealistic;
  ordinary ones (3-deep list patterns, equality on a 40-constructor enum)
  check in under 0.1 s. A fix that would remove both the cap and the cost:
  compile number patterns to comparisons (`n == 404`) instead of `Succ`
  chains, which needs case trees that can branch on a test.
- **Solving metavariables without recursion** (low priority: only large
  literal values in types hit it): `solve`, `rename`, `prune` and `zonk`
  still recurse over a solution. They're guarded, so a deep one is
  `E-RESOURCE`, but they share the stack: in the CLI,
  `theorem a : [1, …, n] = [1, …, n]` checks up to n = 56,875 with `rfl` but
  only 26,875 with `sym rfl`, whose hidden arguments are solved to the list.
- **DESIGN.md §16 open questions** that are still open (universes, handler
  admissibility and semantics, effects and dependency, `withFuel`, `Float`,
  the CLI name).

## Known issues

- **Row order is fixed by declaration order**, so `IO` (declared in the
  prelude) always comes first in a row: `{State Nat, IO}` and
  `{IO, State Nat}` are the same type. Harmless, but it means no test can
  put `IO` on the right of a row.
- **A misleading follow-on error** (found by the IO lane): after an
  `E-UNKNOWN-NAME` earlier in a file, a later `rfl` proof over a handled
  computation failed with "`rfl` proves an equation, but the expected type
  is `runPure (bind …)`". It checked once the first error was fixed.
- **In WebAssembly the stack guard measures the wrong stack.** Each call uses
  both the stack in linear memory (which the guard measures) and the
  engine's own call stack (about 1 MiB in V8), and the engine's runs out
  first. So the guard is set to 128 KiB there (`crates/web/build.rs`),
  calibrated in Node and Chrome only; Firefox and Safari are unmeasured.
  Eliminating recursion (steps 3 and 4) is the real fix.
- **A failed declaration stays declared without a body**, so later
  declarations in the same module can use it. Safe only because a module with
  any error is rejected as a whole. Consider removing failed declarations.
- **The machine starts a nested machine** when a native forces an argument
  that's a solved metavariable (elaboration only). Bounded by the term, not by
  program depth, but it's the one exception to "no re-entry".
- **Memory per frame:** a million-deep recursion peaks at about 750 MB; the
  default limit is 2 million frames.
- **The differential test overflows in debug builds:**
  `the_evaluators_agree_on_the_prelude_and_every_example` overflows its
  64 MiB thread in a debug build (already so before step 4); release builds,
  which the gate uses, pass.
- **Agents' clean-up can hit the user's processes:** the depth-guards lane
  ran `pkill -f serve_forever`, which stopped the local playground server.
  Agent prompts now say to stop only processes they started, by PID.
- **Remaining surviving mutants** judged equivalent or unreachable:
  `effects.rs` lines 223 (×3), 403, 414, 706 (×2), 709, 745, 844;
  `termination.rs` line 111 (`>` → `>=`); the `auto` fix in step 1 (masked
  by the sticky budget).

## Recently done

- `ccebba3` Syntax colouring in the playground's editor (CSS Custom Highlight API, with a fallback); restoring the saved draft on reload fixed.
- `d166039` Stack-safe step 4 (depth-guards lane, merged): every recursive pass guarded by stack use; deep nesting is `E-RESOURCE` natively and in WebAssembly (`crates/driver/tests/nesting.rs`).
- `f35f1a7` Text step 6 (playground-run lane, merged): the playground's Run button and its compiler in Web Workers, replaced after a crash. View it locally with `web/serve.sh`.
- `65f91ce` Text step 5 (run lane, merged): `main` and `stitchwort run`, tested against `simulate` and real standard input and output; `examples/accept/adder.sw`.
- `3fb4764` Text step 4 (IO lane, merged): the `IO` ability and `simulate`, `examples/accept/io.sw`, `examples/extract/io.sw`.
- `fae5cc2` Stack-safe step 3: `conv`, `unify` and `quote` as work lists; iterative freeing of terms.
- `78a9ddc` Local WebAssembly test page: `web/stress.html`, served by `web/serve.sh`.
- `5caa024` `unsafe` allowed with a written justification (lint `deny`, was `forbid`).
- `cdfae0d` Stack-safe step 2: the abstract machine, the reference evaluator, differential tests, iterative freeing of values.
- `14ac90d` Every sub-term the evaluator runs is behind its own `Rc`.
- `2942e55` Checking computes an argument only when a type needs it.
- `e53c53f` Stack-safe step 1: resource errors and per-operation budgets.
- `02235d8` Constructor fields shared (fixed quadratic list recursion).
- `0878284` Text step 2: `Text`, its operations and laws, `++`.
- `01313d1` Text step 1: `Char`, literals and escapes.
