# SW-3172 review: smaller stack frames in checking, unification and zonking

Independent code review (Opus, paper lane, 13 Nov 2026) of `lane/SW-3172`,
`git diff main...HEAD -- crates/elab` (commits 36100205f, a84724692,
14dd9727a) and the new test (b63f30619). Read-only: nothing was built or run.

## Verdict: SAFE TO MERGE

I found no behaviour change for programs that check within their resource
limits. Every rule, arm and fallback is tried in the same order, with the same
guards, the same forcing points and the same effects. The only intended
change in what the user sees is where the stack guard trips (see M1), and that
is the point of the ticket. I have two non-blocking follow-ups (M1, L1) and
some notes.

## What was checked, and how

The old and new text of each function were compared line by line (old from
`git show main:…`).

### 1. `unify_step` (unify.rs:1346 onwards)

- **Two calls of one definition.** The old code had three consecutive `if`s,
  each guarded by `Call, Call, i1 == i2`:
  1. `same_arguments_solving_nothing` → `true`
  2. all-unknown arguments ∧ blocked → `same_arguments` + `note_lossy` →
     `true`, otherwise fall through
  3. `argument_checks > 0 ∧ !solving_arguments` → `false`

  The dispatcher now tests `Call, Call, i1 == i2` once and calls
  `same_calls`, which runs the three in the same order and returns
  `Some(true)`, `Some(true)`, `Some(false)`, or `None` to fall through. Rule
  2's fall-through when `same_arguments` fails, with the trail not undone,
  is kept. Equivalent.
- **`unforced_rules`**: `one_step_apart`, `same_field_calls` (push, then
  `true`), `meta_against_call`, in the old order, before any forcing.
  Equivalent.
- **`forced_rules`**: forces `a` and then `b` at the same point as before.
  The rules for folded dictionaries, sums read again (`a`, then `b`),
  `plus_rule`, `native::compare` (now with `.map(Forced::Answer)`, the same
  value) and `row_rule` keep their order and guards. When no rule applies,
  `Forced::Shapes(a, b)` hands over the forced values, so nothing is forced
  twice.
- **`unify_shapes`** keeps the old arms in order, guards included. The
  same-head arm (`same_heads`) and the different-trees arm
  (`different_stuck_trees`) moved out whole: the sealed/U5 path, the
  blocked/U3 path with `note_lossy`, `may_mention_meta`/shortcut, the
  `opens_by_tree` path with both `undo_since` calls, and the U4 spines-or-eta
  path.
  - `push_equations` replaces `push_all`. It pushes the same pairs in the
    same reversed order. It clones each value once instead of twice; the
    values are the same.
  - `push_fields` is record-eta rule 1, unchanged. The
    `std::ptr::eq(n, a)` test that picks `unforced_a` or `unforced_b` still
    holds. `a` is now `&forced_a`, which `unify_step_rest` owns, and `n` is
    bound by matching `(a, b)`, so `n` points into `*a` exactly when the
    neutral is on the left, as before.
  - `fresh` is now made at the top of `unify_shapes` rather than after
    `row_rule`. It is pure (`Value::var(level)`).
- **`run`**: `run` → `run_outermost` (holds the `CallMemo` `Scoped` guard for
  the whole of `run_tasks`) or `run_tasks`. The `RefCell` borrow in
  `if g.attempt.call_memo.borrow().is_none()` is a temporary of an `if`
  condition, so it is dropped before `Scoped::set` borrows mutably. There is
  no `BorrowMutError` risk.
  - `open_calls`: `call_key` → `known_different` → push `Task::Open`, as
    before. On "known different" the caller still runs
    `record_different(g, &work)` with nothing pushed, then returns `false`.
  - `values_differ`: stale → afresh; blocked → `Later` at the bottom of the
    list; otherwise `note_unfilled` + `sets_aside`. Same order. It is reached
    only when `unify_step` returns `Ok(false)`, through `||`, as before.
  - `other_task`: `Proof`, `Later` (both arms, with the trail guard first),
    `Codomains` (both arms). The arms don't overlap, so moving `Values` and
    `Mode` ahead of them changes nothing.
- **`?` and open-call records**: `Task::Open` is still pushed before
  `unify_step` and popped by the existing top-of-loop path. No `?` lies
  between a push and its matching pop that wasn't there before. Every early
  return through `?` in the new helpers corresponds to a `?` at the same
  point in the old body.

### 2. `check_inner` / `check_value` / the argument loop (check.rs)

- **`check_inner` → `check_special`**: the probe, `Interpolated`, brace
  arguments, named constructor calls, forcing, `check_clause_result`, the
  divergence case body, computation mode, `may_perform_at` and
  `name_unknown_type`, in the same order. It returns `Special::Done` or
  `Special::Value(forced)`. The caller then calls `check_value` (plain) or
  `check_comp_value` (`framed` with `CompFrame`), passing the original
  `expected` as `named`, exactly as before. The old `let g = cx.g()` is no
  longer live across `check_value`. `Ctx::g()` is `self.e.ev()`, a bundle
  of shared references to `Elab`, so reading it again later is the same
  value. This also covers `implicit_lambda` and `explicit_lambda`, which now
  call `cx.g()` after `bind`.
- **`check_value` arms** moved out whole: `unit_type`, `hole_against`
  (hole log, then `proof_holes`, in order), `tuple_type`, `pair_literal`,
  `implicit_lambda`, `explicit_lambda`, `rfl_against_equation` (the four-way
  `||` chain in order, then `cx.unify` for the message),
  `rfl_against_other`, `list_literal` (unchanged, including chunking), and
  `ctor_against`, `ctor_fields_against` and `quotient_against`.
  - `explicit_lambda` rebuilds the rest of a multi-name lambda with
    `Box::new(body.clone())` where the old code used `Box::clone`. Both
    allocate a fresh deep copy, so the value is equal and neither keeps the
    address. Expression addresses are used as keys (`app_expected`,
    `decl.condition`), but those are taken from the original AST and
    scoped, so they are unaffected.
  - A pre-existing quirk is preserved: in `implicit_lambda` and
    `explicit_lambda`, a `?` on `cod.apply(...)` after `bind` returns
    without `cx.reset(mark)`, just as the old arms did.
- **The argument loop**:
  - `Held::start` computes `queued_from`, `metas_from` and `expecting`
    (with the `app_expected` borrow scoped to the `let`) at the same point
    as before: before the loop. The old code built the `Held` struct after
    the loop, but its inputs were computed at the top.
  - `lambda_arg`: same sequence (`insert_with`, `function_parts`,
    `late_able`, in-place check / SW-2638 hold / trial with
    `in_place_trial` ± again / restore + `first_error` + hold).
  - `named_arg`, `piped_arg` and `default_arg` are verbatim.
  - `explicit_arg` = `explicit_arg_ready` (`insert_with`, `hole_of`'s
    force, `function_parts` with `not_a_function_hint`, the proof-search
    hold, the late-literal hold, `next_is_unit`, the snapshot condition) →
    `check_arg` → `explicit_arg_checked` (`note_origin`, the function-name
    force, `apply_lazy`) or `explicit_arg_failed` (no snapshot → hint;
    restore; `unsolved_in`, if none → hint; `first_error`; hold).
    `args[i + 1..]` became `later`, and `args.get(i + 1)` became
    `later.first()`. These are the same.
  - `function_name` is `Some` only from the successful plain path with an
    `Expr::Var` whose domain is an explicit Pi. Every other path returns
    `None`, matching the old `take()` with no reassignment.
  - `Snapshot` is plain data (no `Drop`), so keeping it in a `Box<Checking>`
    and dropping it slightly later has no effect.
- **The boxed first error**: `get_or_insert_with(|| Box::new(e))` keeps the
  first, like `get_or_insert(e)`. `apply_args_once` unboxes with `map_or`.
  `finish_application` unboxes in the one place that returns it (`*first`),
  and its two `*first_error = None` resets and the `E-CANNOT-INFER` test (now
  through `Box` deref) are unchanged. The error it reports is identical.
- **`propagate`**: split into `propagation_plan` (boxed `Propagation`),
  `Propagation::apply` and `propagated`, with `propagate_failed` for the
  failure path.
  - `with_pipes` is recomputed for the name loop, for `apply` and for the
    failure path's `in_same_argument`. It is deterministic. `Arg::Piped`
    refers into `pipes`' heap buffer, which doesn't move when the `Vec`
    moves into the box, and no code keys on a `Piped`'s address.
  - The order is the same: `budget.nesting(PASS)?` first, then
    `apply_args_with`, `Loc`, `insert_with`, the supply check, `compare`.
    On a non-fatal error: `snapshot.restore`, then re-elaborate with
    `no_propagation`/`no_hole_propagation` raised and lowered, then the
    SW-931 same-argument choice.
- **`fallback_named`**: `fallback_pipe` (`(**value).clone()` → `value.clone()`
  on `&Expr`, the same) and `fallback_inferred` (verbatim tail).
- **`queue::framed`**: `enter_frame` and `leave_frame` are always paired.
  `body(cx)` is called without `?`, and `leave_frame` runs before the
  result is matched, as before. `map_in_frame` and `give_frame` are
  verbatim, with `frame` called at the same points (only on a non-fatal
  error, or when items still wait).
- `goals::note_probe`: only the slow part moved to `note_probed`; the cheap
  early returns stay inline. The other files only gain
  `#[inline(never)]`/`#[inline]`.

### 3. `zonk_changed` (unify.rs:3569)

- The arms stay in order. `lifted_call` is called twice, in the guard and
  inside `zonk_lifted`, as before.
- `zonk_solved`, `zonk_let` and `zonk_cases` are verbatim moves. Their local
  `go`/`or` closures capture the same `lets`, `keep` and `depth + 1`, and
  the *effective* `changing` (the caller's local, which may point at the
  caller's `found`). This is what the old closure captured.
- The `Changing` set is keyed by `*const Term`. The helpers receive the same
  `&Term` into the tree, so the keys still match.
- `Eq`, `J`, `Proj`, `Quot` and `Loc` moved back into `zonk_changed`
  verbatim. The `unreachable!` in `zonk_cases` covers only `Case` and
  `NumCase`, which are the only kinds the caller sends.
- The clippy change from `Ok(refold(..)?)` to `refold(..)` compiles, so the
  error types are the same and no `From` conversion was lost.

## Findings

### Medium

**M1. The stack-guard threshold moves, and only one shape was measured.**
`budget.nesting` compares the *stack position* with the floor, so where
E-RESOURCE trips depends on frame layout.
- That is intended for nested applications, which drop from 12.6 KiB to
  5.3 KiB a level, measured by the lane.
- Some recursions now pass through more, smaller frames:
  - a sealed/blocked or U4 comparison now recurses through `unify_step` →
    `unify_step_rest` → `unify_shapes` → `same_heads` → `nested` → `run`
    instead of `unify_step` → `nested` → `run`;
  - nested lambdas through `check_value` → `explicit_lambda` → (`framed`) →
    `check`;
  - implicit Pis through `implicit_lambda`.
- Each extra frame costs a return address, saved registers and alignment.
  The total per level is very likely smaller than the old frames, which were
  sized for every arm, but nobody measured it. A shape that is close to
  320 KiB in the playground today could, in principle, get worse.
- The existing adaptive tests in `crates/driver/tests/elaboration/nesting.rs`
  print each threshold (`threshold N`): `nested_functions_and_function_types`,
  `nested_patterns`, `long_blocks`, `nested_parentheses`. Run a few of them
  by name on `main` and on the branch (release, one at a time) and compare.
  That would show any regression cheaply.
- This is not a merge blocker: no checked program's result changes unless it
  was within a few levels of the guard.

### Low

**L1. The new test hard-codes 40 levels under 320 KiB of native stack.**
`nested_applications_under_the_playground_guard` (nesting.rs:113):
- At the measured 5.3 KiB a level, 40 levels need about 212 KiB, which
  leaves about 50% headroom. At 12.6 KiB it would have needed about 504 KiB
  and failed, so the test does tell old from new.
- Frame sizes depend on target, LLVM version and opt-level. `task test:one`
  and the flake's nextest run are release builds; the only dev-profile run
  is `debug-builtins` (`--test builtins` only). So it is safe in the current
  gates, but a plain `cargo test` in the dev profile would probably fail it.
- Optional: a comment saying it assumes a release build.

### Notes (no action)

- **Small costs added**: one heap allocation per explicit argument checked in
  place (`Box<Checking>`), one per propagation plan, and one per held first
  error (rare); `with_pipes` is rebuilt three times when `pipes` is
  non-empty. None of them changes results, steps or budgets. If the
  orchestrator keeps performance-log entries for such changes (D3444/D3447),
  this one has a stack win and a small allocation cost.
- **Native vs WebAssembly**: the test measures native stack. In WebAssembly
  only address-taken locals live in linear memory, so the playground's
  per-level figure differs. The claim that 40 levels fit the playground is
  only inferred from native.
- **Behaviour equivalence** is argued here by reading only. The verifier's
  hash snapshots and the example kinds are the empirical check, and should
  run on this batch as usual (elaborator change).

## What the new test does and doesn't cover

**It covers:**
- 40 nested `f (… 0)` applications of a one-parameter `Nat → Nat`
  definition, checked against `Nat`, under a 320 KiB guard, in a child
  process;
- that this checks with no error.

That exercises `check` → `check_inner` → `check_value` → `fallback_named` →
`propagate` → `apply_args_postponing` → `explicit_arg` → `check_arg` per
level. It also exercises `queue::framed` if `check_arg` frames.

**It doesn't cover:**
- lambda, named, piped and default arguments;
- the held paths: proof searches, late literals, `after_expected`, and so
  the boxed first error, `explicit_arg_failed` and `lambda_arg`'s trial;
- propagation failure (`propagate_failed`);
- deep unification: the comparisons here are `Nat` against `Nat`, so
  `same_calls`, `same_heads`, `forced_rules` and `run_outermost` recurse at
  most one level;
- deep zonking (`zonk_let`, `zonk_cases`);
- computation-typed contexts (`check_comp_value`);
- any assertion that terms, hashes or diagnostics are unchanged (that is
  left to the hash snapshots and examples);
- the WebAssembly build itself.

The commit message's unification and zonking savings (2.3 KiB, 1.7 KiB and
1168 bytes a level) have no test.

## Suggested tickets

1. Compare the stack thresholds of the adaptive `nesting::*` tests on `main`
   and on the branch, to confirm no other recursion shape got deeper (M1).
   Sonnet or DeepSeek, about 15 min, a few named tests.
2. Optional: a nesting test for deep unification, two calls of one
   definition compared through their arguments, `f (f (… ?x))` against
   `f (f (… 0))`, under the 320 KiB guard, to lock in a84724692's saving.
