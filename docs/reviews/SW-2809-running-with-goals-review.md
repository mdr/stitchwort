# SW-2809 review: running with open goals (D3507)

Paper review (Opus, 11 Nov 2026) of `lane/SW-2809` at `ab1b7dcb8`. Read
only: nothing was built or run. Line numbers are in that commit. Background:
docs/proposals/using-unfinished-proofs.md §5.6, D3507, and
docs/reviews/SW-2804-assumptions-review.md F1/F7.

## Verdict

The structure is right, and with no goals nothing changes in practice:
every edited path only fires when a run reaches code that a program whose
proofs are all checked never reaches. Reaching a data `?` stops cleanly on
the evaluator, the machine, native code and built executables, and names
the goal. Two things block shipping:

- **MUST-FIX 1 (D3507 gate).** The three known gaps are real: a false cast
  gives a wrong answer on native and JS, a false `Array.getLt` bound panics
  the machine and aborts native code, and a `decreasing := ?` loops.
  D3507 says such a gap goes back to Matt before shipping. The `getLt` one
  is also a regression for `test` under `warn`: a test that was skipped
  (SW-2793) can now panic or abort the whole `stitchwort test` process and
  lose every result. Its fix is nearly free (§6b), so do it in this lane.
- **MUST-FIX 2.** In JS, an impossible branch reached while the module
  loads is not mapped to exit 73 (`js/src/run.rs:1055`, below). It's a
  one-line fix.

The SHOULD-FIXes are about naming and reporting. The biggest is that JS
throws for a goal-dependent constant when the module loads, so a
`build --js` library with one such constant can't be imported at all (§4).

## 1. Every runner stops cleanly; no change without goals

| Runner | Where | Verdict |
|---|---|---|
| Evaluator (`run --reference`, `test`, `eval`) | `core/src/value.rs:1504`, `:1527-1531` (data assumption while `program_running`), `:2284-2290` (empty `case` on the erased placeholder), `:2320-2330` (impossible branch, was `panic!`) | OK. All three set `Erasure::reached` and return `ResourceError::Unreachable`. `quick` returns `None` (`:1504`), so it falls through to `eval_step` and never makes a neutral. |
| Machine (`run`, `test`, built executables) | `rt/src/lower.rs:156-164` (the assumption is a constant whose body is `Unreachable`), `rt/src/machine.rs:1610-1616` | OK. Constants are computed lazily (`machine.rs:1193-1199`), so `two` stops the run only when it's used. The current frame is `st.frames.last()` (`save!` at `:1149`), so `reached` names the constant's own code. The error returns the same way `Work` does from `enter_frame`. |
| Native | `native/src/n1.rs:4344-4352`, `rt/src/native_abi.rs:1090`, `:1410`, `:1472-1476` | OK. Every call site checks `ERROR_AT != 0` (`n1.rs:2014`, `:3702`, `runtime.rs:495`), so `UNREACHABLE = 3` unwinds like the step limit does. A goal constant computed through `NativeExecutor::global` goes through `cross`, which records `reached`. |
| Built executables | `standalone/src/lib.rs:238-247` via `RunError::diagnostic` | OK for a goal. For an impossible branch see S5: the wording claims a false goal even when there are none. |
| JS `run --js` | `js/src/lib.rs:6078-6100` `goal_stopper`, `js/src/run.rs:974`, `:1055` | Stops, but at module load for constants (S1), and the load-time handler misses impossible branches (MUST-FIX 2). |
| `build --js` libraries | `js/src/lib.rs:994`, `js/src/run.rs:151` | Builds. Importing the module throws if any reachable constant needs a data goal (S1). |
| `test` | `driver/src/test_run.rs:516-528` | Stops, but only through the evaluator: native and the machine give up and pass the test on (S3). |
| `eval`, REPL | `elab/src/lib.rs:944-963`, `cli/src/main.rs:3985-3989` | OK. N2 and N3 are smaller issues. |

**No goals, no change: OK.** Each change, with no goals:

- `value.rs:2320-2330`: the `panic!` becomes an error, which an all-checked
  program never reaches (indexed-families §6.8).
- `value.rs:2284-2290`: an empty `case` on the placeholder. A running
  program holds a placeholder for `Void` only through an unchecked proof, so
  this is unreachable too (an inconsistent `axiom` aside, which is already
  unsound).
- `machine.rs:1610` and `n1.rs:4347`: `Instr::Unreachable` is reached only
  by an impossible branch, an empty Prop `case` (`lower.rs:1359` and the
  other `branches.first()` cases), or a failed rebuild check
  (`lower.rs:1608`, `checked` mode). The last is a compiler bug. It used to
  panic; it now gives `E-INTERNAL` ("reached a branch that can't be
  reached", `driver/src/run.rs:313-320`). That's still a failure, just
  exit 2 instead of 101.
- JS: an impossible branch's `Error("unreachable")` used to be rethrown
  (exit 1, a Node trace). It is now exit 73, which the CLI turns into
  `E-INTERNAL` when there are no goals. That's better.
- `test`: with `with_goals = false`, `runs()` is `!is_unfinished`, as
  before (`test_run.rs:557-563`), and `lower_tests` filters the same way.
- `main_call` and `refuse_unfinished` changed from `is_unfinished` to
  `state() != Final` (`driver/src/run.rs:187`, `driver.rs:944`). With no
  goals the two agree.
- No codec or format bump is needed: `Expr::Unreachable` was already
  encoded (`codec.rs:182`), and nothing that relies on a goal was ever
  lowered, so no cached program is stale.

## 2. `ResourceError::Unreachable` and the "reached" bookkeeping

**The variant: NOTE, keep it.** `ResourceError` is the evaluator's only
error channel (`Result<Value, ResourceError>` everywhere), so a separate
type would mean changing every eval signature for one case. The doc says
honestly that it's "Not a resource" (`budget.rs:56`). It's produced only
while `program_running` is set, which the kernel never sets, so checking
can't see it. `Diagnostic::from` special-cases it (`budget.rs:84-90`).
Later, a rename of `ResourceError` to something like `Stop` would make the
name honest; it isn't worth doing now.

**Bookkeeping: OK, with two misreports.**

- `Erasure::reached`, the machine's `st.reached` and the native
  executor's `reached` are never cleared, but each is set on every path
  that raises `Unreachable` and read only right after one. So none goes
  stale in practice.
- **Misreport A (S3).** Under `test`, Unreachable on native or the machine
  is thrown away. `NativeTestRun::run` turns it into `Err(e.to_string())`
  (`test_run.rs:125`), with a misleading note: "test … runs on the machine:
  the program reached …". `TestMachine::run` gives `None` (`:220`). The
  test then runs a third time on the evaluator, which is what produces
  `Stopped`. A test that does a lot of work before reaching the `?` can run
  out of the evaluator's limits first, and is then reported as
  *unfinished* (`OutOfResources`), not as stopped.
- **Misreport B (S5).** `RunError::Unreachable`'s `Display`
  (`rt/src/host.rs:73-79`) says "a proof it relies on is an open goal …
  whose statement is false" for any impossible branch. The CLI words it
  better (`unreachable_diagnostic` falls back to `E-INTERNAL` when there
  are no goals), but a built executable uses `Display` directly
  (`standalone/src/lib.rs:242`), so a compiler bug there would blame a
  goal that doesn't exist.
- NOTE: native names the body by `self.code_index`. If n1 ever inlines
  across bodies, an impossible branch would name the caller. That only
  affects the message.

## 3. Native: the `UNREACHABLE` exit instead of a trap

**OK.** Nothing relied on the trap for soundness. The trap only decided
what happened *after* the branch was reached; whether it can be reached
depends on the kernel's check and on lowering keeping every arm:

- `Switch` tables have one entry per constructor (`code.rs:1010-1023`), and
  their default is still `self.trap` (`n1.rs:4241`).
- The optimiser keeps the test of a match whose other arms are
  `Unreachable` (`opt.rs:983-1013` keeps the `Match`). It folds only
  constants that are constructors (`opt.rs:280-286`), so a goal constant is
  never inlined. `ctor_leaves` leaves out `Unreachable` leaves only to
  count leaves (`opt.rs:204-219`); the copied code still contains them.

So an impossible branch with no goals is exactly as impossible as before.
The new code runs `exit_now` at a new kind of pc. `exit_now` is
pc-generic and already runs at every step-limit check, including with lent
registers live, so I see no new risk. The other `trap(4)` and `trap(1)`
sites (helpers, falling off the end) are unchanged.

NOTE (performance): every impossible branch in std now compiles to a full
exit (spills, a `sw_unwind` call, a return) instead of one `trap`. That
makes native code larger and slower to compile. A cheaper version: one
shared cold block per body that stores `REACHED_AT` and jumps to
`shared_exit`, as `call_result` does for `in_file` (`n1.rs:3709`). If it's
measured, it gets a performance-log entry.

## 4. JS

- **MUST-FIX 2. A load-time impossible branch isn't mapped**
  (`js/src/run.rs:1055`). The worker's `error` handler checks only
  `e.name === "Unreachable"`. Take a constant computed through an
  impossible branch, for example
  `def x: Nat := List.getLt [1, 2] 5 [ok := falseGoal]`: it throws
  `Error("unreachable")` while the module loads, so the run gets
  `console.error` and exit 1 instead of 73 and `E-UNREACHABLE`. Fix: add
  `|| e.message === "unreachable"`, as at `:974`.
- **S1 (SHOULD-FIX, possibly a decision). Constants throw at load**
  (`goal_stopper`, `lib.rs:6094-6098`). This is a real difference from the
  other runners, and the CLI test documents it (`open_goals.rs`, "JS
  computes a module's constants as it loads"): machine, native and
  reference print `start\none\n` before stopping; JS prints nothing. It's
  worse for `build --js` libraries, where importing the module throws, so
  every export becomes unusable, including those that never touch the
  goal. Fix: JS already has `Convention::Thunk` (`lib.rs:2240-2246`, used
  as `f()` at `:4647`). Give `Thunk` to a data assumption of arity 0, and
  to every constant that relies on one (`assumption::relies_on`, which is
  already memoised in core). Make it a memoising thunk if constants are
  shared, since only goal-dependent code pays for it.
- NOTE: `goal_stopper` decides between "function" and "constant" by
  whether the type is a `Pi` (`lib.rs:6091-6094`). But the assumption's
  JS convention comes from its runtime mask (arity 0, so `Value`).
  Consider a goal of type `(a: Type) → List a`, whose only parameter is
  erased. It is emitted as `() => throw`. If callers pass nothing for erased
  parameters of a function value, it's then used as a value (a JS function
  where a list was expected) and never throws. Check how JS applies a
  value-convention global to only-erased arguments, or decide from the
  runtime mask instead.
- Exit 73 is new, and nothing returned it before. Programs without goals
  can produce it only through a compiler bug (§1). `e.message ===
  "unreachable"` can't come from user code: `Fail` is a `FailError` and is
  checked first (`run.rs:965`).
- NOTE: `Error` objects keep their own properties when they cross the
  worker boundary, which the JS case of
  `run_warns_and_stops_at_an_open_goal_it_reaches` covers. That test is
  skipped on a machine without `node`.
- SHOULD-FIX (S4, docs): `goal_stopper` was inserted between `def_name`'s
  doc comment and `def_name` (`lib.rs:6069-6078`). `def_name`'s doc now
  sits on top of `goal_stopper`'s, and `def_name` has none. The same
  happened at `rt/src/machine.rs:239-249`: `depth_report`'s doc is now on
  `unreachable_at`.

## 5. `test` under `warn` running tests that rely on goals

- OK: `Stopped` is a failure in the counts (`main.rs:2119`), in JSON
  (`main.rs:2009`) and on the web (`web/src/lib.rs:241`, `:268`), and it's
  never cached (`driver.rs:1384`, `:1430`, `:1449`).
- OK: a pass that relies on a goal is cached under a hash that covers the
  assumption (`a_user_s_hash_covers_the_assumption`), so filling the goal
  invalidates it. Under `fail`, such tests aren't run or shown, as before
  (`test_run.rs:432`).
- **S3 (SHOULD-FIX):** see Misreport A in §2. In `TestMachine::run` and
  `NativeTestRun::run`, turn `Unreachable` straight into
  `Outcome::Stopped`. Take `reached` from `unreachable_at()`, mapping the
  global's path to its `DefId` as `unreachable_diagnostic` does, and don't
  fall back to the evaluator.
- **S2 (SHOULD-FIX, naming):** `run_tests_where_skipping_unfinished`, its
  `_fast_` and `_native_` versions (`test_run.rs:248-262`, `:286-300`,
  `:322-335`) and their docs still say "reporting … as skipped". They now
  run those tests. Rename them `*_with_goals` and fix the docs.
- **Decision for Matt (D-new, small):** a test that relies on a goal and
  passes prints a plain `✓`, the same as a real pass. `test` prints no
  "running with N goals" line (the `check` summary's "N goals open, allowed
  …" is the only sign). D3507's "clear that those issues exist" suggests
  marking such passes, for example `✓ orTwo True  (relies on `two`'s
  goal)`. [rec: yes, mark them; it's cheap, since `goals_relied_on` per
  test already exists.]
- With a false proof goal, `test` is the worst-placed runner. The cast
  gap's evaluator and machine invariant panics, and the `getLt` panic and
  abort, take down the whole test process, not one test. That's why
  MUST-FIX 1 includes the `getLt` fix.

## 6. The known gaps

All three are as the commit describes them. I confirmed them by reading
the code, not by running anything.

**(a) A false cast.** `J` on the placeholder takes its base
(`erase.rs:17-23`). A single-constructor match has no `Switch`
(`code.rs:1003-1009`), and n1 and JS read fields without checking the tag,
so a mistyped value goes on unnoticed: `flipped to true`, exit 0.
Confirmed.

**(b) `Array.getLt` with a false bound.** On the machine,
`prims.rs:899-903` panics with "`Array.getLt` out of range, against its
proof". Native reaches the same prim through a helper (n1 special-cases
only `Set` and `GetOr`, `n1.rs:4933`, `:4978`), and a panic inside an
`extern "C"` helper aborts. In JS, `(a) => (i) => arrayItems(a)[Number(i)]`
(`js/src/lib.rs:5738`) returns `undefined`. That is a `TypeError` only if
something later uses it arithmetically; `undefined === 3n` is simply false,
so it can also be a silent wrong answer. The commit's "TypeError" is the
lucky case. The evaluator has no native for `Array.getLt`: it runs
`List.getLt`, whose `[]` arm is `Void.absurd` on the placeholder, so it
stops cleanly (`value.rs:2284`).

**(c) `decreasing := ?`.** The erased measure proof gives the compiled
recursion nothing to stop on. A tail-recursive loop runs forever, since
`run` has no step limit; a non-tail one ends with `E-RESOURCE` (depth),
with no word about the goal. I didn't trace how the `decreasing` goal's
assumption appears in the lowered term.

### Fix sketches, cheapest first

**(d) A run-time bound check, so a true-but-unproved bound still runs.**
For `getLt` this is almost free, because the machine and native already do
the bounds check (`.get(i)` returns an `Option`). Only the failure action
changes:

- Machine and native: on `None`, stop with `ResourceError::Unreachable`
  instead of panicking. `array` returns `Value`, not `Result`, so
  special-case `GetLt` in the machine's prim dispatch, as
  `Replicate`/`TextFold` already are (`machine.rs:1290`, `:1309`). The
  native helper sets `context.error = UNREACHABLE` and returns. That costs
  nothing on the success path.
- JS: `(a) => (i) => { const xs = arrayItems(a), n = Number(i); if (n >=
  xs.length) throw new Error("unreachable"); return xs[n]; }`, which is one
  comparison. Don't test for `undefined`, since erased elements can be
  `undefined`.

A true bound with an unproved proof runs exactly as now; only a false one
stops. The CLI's message is then "reached a branch that can't be reached
in `Array.getLt`: one of the open goals it relies on is false; it relies on
`inRange`'s goal". That is clear enough for D3507. With no goals, the same
check reports `E-INTERNAL`, as a broken invariant should. I recommend this
in this lane.

**(e) The general fix: check a decidable goal where its proof is used.**
This one mechanism covers bounds, decreasing measures and index-equality
casts, and needs no kernel change:

1. When the elaborator turns a proof `?` into an assumption, it tries
   instance search for `Decidable (goal)` in the hole's context. This
   builds on the Decidable work under way. On success it adds an ordinary,
   checked companion `half.?1.decide : ctx → Bool`. The assumption itself
   and its hash are unchanged; the companion is code, not a premise.
2. A proof argument is erased, but its term is still in the kernel term.
   Where the term is the assumption applied to its context
   (`half.?1 x y`), every runner evaluates
   `if half.?1.decide x y then <erased> else stop(at = half.?1)` at that
   point:
   - evaluator: in `eval_step`'s erased-assumption arm (`value.rs:1523`);
   - machine/native: in lowering, where the erased argument is dropped;
   - JS: in codegen.
3. The new stop reads "the program reached `inRange`'s goal (m.sw:5),
   which is false here: `5 < 3`". That needs a third case in
   `RunError::Unreachable`, or an `is_false: bool`.

What it catches: `i < length` (the (d) case in general, for `List.getLt`,
`Vec`, user code), `decreasing` goals (Nat `<` on the measure, checked on
each recursive call, so a loop stops at the first bad step), and casts
through equalities of values (`h: 2 = 3`, `n + 0 = n` at concrete `n`). A
true-but-unproved goal costs one decision per use, and only in programs
that rely on goals.

What it can't catch: equalities of types (`Nat = Bool`) and other
undecidable statements. For those, the cheapest safe step is to say so: the
"running with" warning lists them separately ("… 1 of them can't be
checked while running: if it's false, results may be wrong"). The
alternative is refusing to run a program whose cast relies on one.

**Cheapest stopgap for (c) alone**, if (e) waits: when a run ends with
`Work` or `Depth` and the program relies on goals, add a note to the
`E-RESOURCE` diagnostic naming them ("it relies on `f`'s goal
`decreasing`; if that's false the recursion may not end"). That's one
`goals_relied_on` call in the existing error path. It doesn't stop an
endless tail loop, but `run`'s Ctrl-C does.

**Decision for Matt (the D3507 gate).** Recommendation: ship with (d) now.
Make (e) a follow-up ticket on the Decidable epic, and until it lands,
list unchecked proof goals in the warning line. That leaves only
type-equality casts silently wrong, and those are named in the warning.

## 7. Other findings

- **S5 (SHOULD-FIX):** `host.rs:73-79`, Misreport B. Word it as "… can't
  be reached in `x`: either a proof it relies on is a false open goal, or
  this is an internal error". Or have `build` embed whether the program
  relies on goals.
- NOTE: the runners stop at different points. The evaluator is strict, so
  `let x = two in 1` stops there, while the optimiser drops the dead `let`
  on the machine, and JS stops at load. Every runner stops and none gives
  a wrong answer, so this is fine; but the guide's "a run that doesn't
  reach it runs as usual" is only true per runner.
- NOTE N2: `evaluate` (`cli/src/main.rs:3985-3989`) elaborates the
  expression twice, once for the warning and once in `eval_expr`. Have
  `eval_expr` return the term, or the goals.
- NOTE N3: `eval_expr`'s check (`elab/src/lib.rs:944-963`) looks at the
  quoted value. A function value whose binder type or unreduced body
  mentions a data goal (`fun (v: Vec Nat two) => 0`) is refused even
  though nothing reached the goal.
- NOTE: the web playground runs and evaluates without the warning line
  (`web/src/lib.rs:343`, `run_main_in`).
- NOTE: `unreachable_diagnostic` (`driver/src/run.rs:286`) finds `at` by
  `rposition` on path. That's fine, since an assumption's path
  (`half.?1`) is unique.
- NOTE: function-typed data goals stop at different moments on different
  runners: when referenced on the evaluator and machine (a constant), when
  called in JS. Harmless.

## What I didn't check

- I ran nothing, so the claims about Node's error serialisation, native
  `abort` and the `decreasing` loop are from reading the code plus the
  lane's own tests.
- Native AOT `--native` executables beyond `NativeExecutor` sharing the
  JIT path.
- How a `decreasing` goal's assumption sits in the lowered term, which
  (e) depends on.
