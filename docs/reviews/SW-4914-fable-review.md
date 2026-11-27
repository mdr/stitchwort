# SW-4914 (compact test levels, D3758 option (b)): review of the lane's diff

Fable, 27 Nov 2026. Reviewed `git diff main...lane/SW-4914 -- crates docs` (commit
1b5e92d59) against `docs/reviews/SW-4914-fable-analysis.md`, section 5. Marks: **[read]**
from the code, **[run]** from a run of mine, **[inferred]** argued, not traced line by line.

## Verdict: merge

No blocking issue. The invariant holds at every place I could find that makes a variable
during a comparison, running out of levels is an error everywhere, and nothing
depth-dependent is filed. Six small follow-ups below, none needed before merging.

## 1. The invariant [read]

- **Point 1 (raised before the closure is applied): holds at all five sites.** `codomains`,
  lambda against lambda, eta in `conv_step`, `push_eta` and `same_trees_of` each call
  `fresh_past` before the `apply`/`extend` that first uses the variable. I grepped every
  `Value::var`, `var_marked` and `Head::Var(` construction in `crates/core/src`: the others
  are the checker's context variables, read-back (`quote`, context levels, not called from
  evaluation or comparison), `mark_of_type` (at most 32 variables above a caller's `fresh`),
  `determined.rs` and `is_type_former` (section 2). No sixth comparison site.
- **Point 2 (a true maximum): holds.** `fresh_past` only ever raises; within one
  `conv_with` nothing lowers `reached` except the exit of a nested `conv_with` or
  `same_trees_of`, each back to its own entry value, which is at or above everything the
  enclosing comparison had made by then.
- **Point 3 (entry and restore): holds.** `conv_with` takes the guard before any `?`, so
  errors, the stack guard and unwinding all restore. In the kernel the entry raise is in
  fact redundant (every variable at or above `RESERVED_LEVELS` comes from `fresh_past`,
  and a test starts at `max(RESERVED_LEVELS, reached)`); it matters for callers that pass
  a level of their own, which today is only tests. Worth keeping.
- **The guard on `same_trees_of`: right, and complete.** Without it the unifier's calls
  (`unify.rs` 2417, 2471, outside `conv_with`) would leave `reached` raised for the rest of
  the thread: not unsound, but a leak that would also break the "given back" assertions.
  Inside the kernel it lowers `reached` while the enclosing `conv_with` is still running,
  which is safe because `same` is synchronous in both callers (`stuck_same`,
  `stuck_different`: a nested `conv_with`), so every value holding a field variable is done
  with when it returns. The same argument as a nested `conv_with` returning in
  `same_spines`. core.md's point (2) says "over the whole comparison", which this makes
  slightly loose: what holds, and what soundness needs, is "at or above every variable
  still live".
- **Restoring is safe only if no cache evaluates a dead variable's value.** This was "not
  checked" in my analysis; checked now. `CallMemo` matches by level and cell address;
  `TreeMemo` and `ShapeMemo` (the answer memo) by `shape_hash` and `identical_charged`,
  neither of which forces or applies anything (no `force`, `eval` or `apply` between
  `value.rs` 7145 and 7800). An unfolding cell is shared, but it computes from its own
  call's spine, so it can't hold another comparison's variable, and its result doesn't
  depend on `reached` (only an error can, and errors aren't stored).
- **Other entry points.** The elaborator's unifier makes its own levels with a plain
  `level + 1` and never raises `reached`; its variables are context variables, below
  `RESERVED_LEVELS`, so a test met there starts above them as before, and the kernel
  rechecks what it concludes. Its postponed constraints can hold `same_trees_of`'s field
  variables after the guard restores; same reason, no issue. Rule S goes through
  `meet_in_evaluation` (3407, 6656). Memo replays match only.

## 2. The cap, F1 and F2

- **`LEVEL_CAP = usize::MAX - 3` [read].** `next <= LEVEL_CAP`, so the highest fresh
  variable is `usize::MAX - 4`: below all three markers, with one level to spare. F1 is
  closed. `checked_add` closes the 32-bit wrap.
- **`is_type_former` stopping at `RESERVED_LEVELS`: sound [read].** Its variables are
  context variables that `reached` doesn't see, and a cast met while applying a codomain
  starts its test at `RESERVED_LEVELS`, so they must stay below it; `next <=
  RESERVED_LEVELS` is exactly that. The cap would have been wrong here. F2 is closed.
- **Is it a refusal that matters? Not on 64-bit; not settled on 32-bit.** On 64-bit it
  needs 2^40 iterations of force and apply, far past the 10^10 default budget if each
  costs a step, and hours of run time if not. On 32-bit it needs 2^31, under the default
  budget only if a binder costs under 4.7 steps. **I could not measure that**: my probe
  (`def use (f: T 1000000)` with `T` by recursion) checked under
  `STITCHWORT_WORK_LIMIT=1000000`, which means that path doesn't walk the type at all,
  and I stopped there. Either way it replaces behaviour that was already wrong on main
  (past 2^31 the walk's variables were in the tests' range), so it is not a narrowing of
  anything that worked.

## 3. Out of levels is E-RESOURCE [read]

- Kernel: `budget.too_deep("comparison")`, which also marks the budget exhausted, so
  nothing after it can answer. `meet_in_evaluation` has no "not equal" path left. The two
  `.ok()?` at 6645 and 6656 are the stuck-on-a-proof note: a lost message only.
- Reference evaluator: `ends_level` and `fresh_past` return `ResourceError::Nesting`,
  propagated by `?`; `ENDS_DEPTH` is put back before the result is looked at. Its ranges
  are its own arithmetic now, as the analysis asked.
- The answer memo is written only after `conv_with` returned `Ok`, and cleared when the
  outermost test ends, errors included (`ClearAnswers`; "outermost" is now "no memo yet",
  equivalent to the old `used == 0`).
- The elaborator has several `conv(..).unwrap_or(false)`; untrusted, and the exhausted
  budget stops the declaration anyway.

## 4. The test-only check [read, run]

- **Checks the right thing, forces nothing.** It walks function types' domains, closure
  environments, data arguments, constructor fields, spines and stuck casts' motive, base
  and ends; asserts `l < start`, markers apart. It walks a closure's whole environment,
  where `identical` looks only at what the body uses: stricter, and I see no way to a
  false alarm.
- **Not walked:** a call's unfolding cell (right: its variables are its spine's) and
  `Value::Resumption`'s captured frames (a gap, small).
- **On for the soundness examples: yes, in process** (`par_map_sessions`, not a spawned
  binary). **[run]** `examples::soundness_examples_fail_for_the_expected_reason` passes in
  5.9 s with it on.
- **Not on for the fuzzers**, which the analysis asked for. Suggestion 3.
- **It can be slow: see 7.**

## 5. Tests [read, run]

**[run]** All four `rule_k::` tests pass, 13 to 20 ms each.

- `a_test_deep_in_a_comparison_starts_above_it` pins point 1 at the lambda-against-lambda
  site: with the raise removed or moved after the `apply`, the test's `z` is `w` and the
  comparison answers "equal". Its second assertion (`deep - 1`) adds nothing I can see.
- "Given back" is pinned on return, on error and at the outermost end.
- `a_test_out_of_levels_has_no_answer` pins the error, the unchanged state and recovery.
- `many_nested_tests_fit_a_32_bit_space` pins that 150 nested tests are answered.
- **Not pinned:** point 3 (drop the entry raise and every test still passes: the deep
  test's `fresh_past` raises anyway, and the nested test sets `reached` by hand); point 2
  (a `fresh_past` that sets rather than raises); the other four sites one by one.
- I could not find the lane's mutation check in the commit message or the ticket, so the
  above is from reading, not from its description.

## 6. docs/core.md [read]

Accurate, including the consequence (a cast fired with unequal ends, subject reduction
lost, no known route to `False`) and the unconditional memo sentence. Three wording nits:

- "`is_type_former` ... stops below 2^40 for the same reason": it is `RESERVED_LEVELS`
  (2^31 on 32-bit), and the reason is a different one (its variables are context
  variables, which `reached` doesn't track).
- Point (2), "over the whole comparison": see section 1; `same_trees_of` gives its
  fields' levels back early.
- "alike on every target": the rule is alike; the room is 2^31 levels on 32-bit.

## 7. Could a new test hang?

- **None of the new tests loops to a large level.** Each sets `reached` or the level
  directly; the deepest work is 150 nested casts. **[run]** 20 ms.
- **The level check is the one new thing that can run very long [read, not reproduced].**
  `check_levels::below` remembers closure environments and constructor fields it has
  seen, but not spines, `Shared` cells or `Elim::J` parts, so a value that shares
  sub-values through stuck applications (`f a a` with `a = f b b`, the SW-2730 shape) is
  walked as a tree: 2^n for n levels of doubling. It also runs on every test, before the
  memo is consulted, and charges no budget steps, so nothing stops it. With the flag on,
  `examples/accept/cast-ends-tested-once.sw` (40 levels, both ends holding the same call)
  is the kind of input I would expect to show it. That would explain a multi-minute hang
  in a run with `STITCHWORT_CHECK_TEST_LEVELS=1` or after `check_levels::set(true)`; I
  can't tell whether it is the one the lane saw.

## Suggestions (possible tickets, none blocking)

1. **`check_levels::below`: remember spines and shared cells by address**, as
   `identical_within` does, so the walk is the value's size in memory. Needed before 3.
2. **Tests for points 2 and 3 and the other four sites.** Point 3: a cast with ends
   `z => z`, `z => w` and `w` free at `RESERVED_LEVELS`, compared with `conv` at
   `RESERVED_LEVELS + 1`, no binder around it. The sites: the same cast under a function
   type's codomain, under each eta, and in a shared `case` branch's fields.
3. **Turn the check on for the fuzzers** (`STITCHWORT_CHECK_TEST_LEVELS=1` in `task
   fuzz:*`), as the analysis asked.
4. **core.md's three wording nits** (section 6).
5. **Measure `is_type_former`'s steps per binder**, to settle whether the 32-bit stop is
   reachable under the default budget; and find which path calls it on a parameter's type.
6. **`check_levels` doesn't walk `Value::Resumption`.**

## Not checked

- No 32-bit build or run.
- Whether `is_type_former`'s loop charges a budget step per binder (section 2).
- The exponential walk in section 7 is from reading; I did not build an input that shows it.
- The differential tests and the examples other than `soundness` were not run (test budget).
- `probe/dtop1.sw` and `etop1.sw` (the 25 to 75 s end-to-end runs) were not rerun.
