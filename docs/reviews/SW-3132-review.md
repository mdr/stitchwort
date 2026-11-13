# SW-3132 review: natives' glued arguments forced in the machine; zonk look-ahead

Reviewed: branch `lane/SW-3132`, commit `8fe37a9a0` (base `3fbc3ba17`), 13 Nov 2026.
Paper review plus probes with the lane's release binary against main's
(`622b03870`, 21 commits ahead of the lane's base, so its extra
`W-ARROW-FORALL` warnings were filtered out before comparing).

## Verdict

**Merge.** No must-fix items.

The evaluator change forces exactly the arguments `native::run` forced, in
the same order, through the same code (`Control::Force` → `force_call` →
`Frame::Unfolded`), so values, normal forms and what the kernel accepts as
equal are unchanged. The zonk change returns `None` exactly where the old
recursion did. What does change is resource accounting: step counts move
by small amounts in both directions, and a deep chain's frames now add up
in one machine. Both are observable in principle through the small
"attempt" budgets; I found no case where a result changed. See M1 and M2:
they are things to know and record, not blockers.

## What I checked

### 1. Soundness (evaluator)

- **Same arguments, same order, same stopping point.** `native::run`
  (native.rs:1051) forces the head of each of the first `numbers()`
  arguments in order and stops at the first whose head isn't a number
  (`number_head`), handing over to `run_partial`. `unforced_number_arg`
  (value.rs:2642) walks the same arguments in the same order, with the
  same all-explicit-spine guard, and asks the machine to force argument
  `i` only when every earlier one is, after forcing, a number head: the
  condition under which `run`'s loop reaches `i` and forces it. On
  resuming (value.rs:1826) a forced head that isn't a number goes straight
  to `run_native`, as `run` would stop there. So nothing is forced that
  wasn't, for every native:
  - `Add`, `Sub`, `Leq`, `EqNat`, `EqNatRefl`: nothing more to say; the
    head loop is the only gate.
  - `Mul` and `DivFuel` (SW-3055's open-number rule): their laziness
    ("never look at `n` when `m`'s head has no `Succ`") lives in
    `run_partial`, reached only after the head loop has stopped at a
    non-number head. The new code stops there too. `NatAdd` (`k + x`) is
    not a `number_head`, so an open number stops the pre-forcing as it
    stops `run`.
  - `EqNatSound`: `numbers()` is 2, so its proof is never looked at.
  - `Outcome::Again` / `Succs` / `UnfoldAfterSuccs`: `run_native` handles
    them as `unfold_now` did; the re-entered `Control::Unfold` goes
    through `from_native` again, where the arguments already have kept
    unfoldings or are fresh values.
- **Conservative cases.** A solved metavariable argument, or a kept
  unfolding that itself still needs forcing, makes `unforced_number_arg`
  return `None`: the native then forces with its own `force` as before
  (correct, only the stack saving is lost for that call).
- **Opaque, hidden, erased, float checks** run once in `unfold_now` before
  `from_native`; the resume path skips them, which is right: none of them
  can change while an argument is forced inside one run.
- **`glue` flag.** `run_native` falls through to `case_tree(…, false)`
  where the old code passed `glue` on. `glues` is false for every
  registered native, and with natives disabled the branch isn't entered,
  so the two are the same.
- **Termination.** The set of forced arguments is the same, so nothing
  diverges or runs out that didn't, apart from the accounting in M1/M2.
- **Kernel.** The kernel glues while checking a body (`admit_group`), so
  this path is live in the kernel. The only kernel-visible differences
  are `E-RESOURCE` outcomes, which reject and never accept (core.md,
  "Running out of budget … is `E-RESOURCE`, never 'different'").

### 2. Sharing and caching

No new cache. "Stored with the call" is the existing `Unfolding` cell,
written by the existing `Frame::Unfolded` with the existing epoch and
mode checks (`Kept::fits`). The frame holds a clone of the spine, which
shares each call's `Rc<Unfolding>`, so the native's `force` finds what the
machine kept. A kept value that doesn't fit the reader (other epoch or
modes) reads as absent and is recomputed, as before. Nothing is keyed by
environment or binder depth.

### 3. Hashes and determinism

Covered under M1 and M2. Step and frame counts are the same in every
build (no address, hash-order or stack-size dependence was added; the
zonk `HashSet` is only queried, never iterated).

### 4. Zonk

- **"Unchanged" is exact.** `zonk_changed` returns `Some` only at a
  metavariable-headed node (`lifted_call`, `meta_headed`), at an
  application `empty_row_done` takes apart, or at an ancestor of one.
  `Changing::of` marks metavariables, `empty_row_done` applications and
  their ancestors. An application that only becomes an
  `empty_row_done` shape after its row is solved has a metavariable below
  it, so it is marked. `Term::Let` needs care: it calls `cheaply` and
  extends `lets`, but `lets` is only read at metavariable nodes, so a
  `let` with nothing marked below it returned `None` before too.
- **All node kinds.** `Term::for_each_child` is an exhaustive match and
  visits every child `zonk_changed` recurses into (`Case` bodies that
  exist, `NumCase` arms and default, `Eq`'s optional type, `Quot`
  arguments, `Loc`, `Proj`, all three parts of `Let`).
- **Address keys.** Only nodes of the scanned term are looked up, they
  stay alive and unmoved for the scan's lifetime (`found` lives in the
  frame at depth 32; children are behind `Rc`), and whether a node can
  change doesn't depend on its context, so a node shared between two
  places gets one correct answer. `zonk_call` and `zonk_in` start again at
  depth 0 with no scan, so a scan never sees a term it wasn't made from.
- **Side effects dropped.** Skipped nodes no longer take a budget step,
  and a skipped `let` no longer runs `cheaply`. Both only remove work;
  see M1 for the step count.

### 5. Tests and probes

Named tests run in the lane's worktree (all pass):

- `stitchwort-core::it glue::natives_force_a_deep_chain_of_glued_calls_in_one_machine`
- `stitchwort-core::it glue::natives_never_glue`
- `stitchwort-elab unify::tests::zonk_goes_down_a_deep_term_only_where_it_changes`

Probes, lane binary against main's, `check --no-cache`, files in
`/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3132rev/`:

| Probe | Main | Lane |
|---|---|---|
| `p1.sw`: `Nat.iterate 2000 inc 0 = 2000 := rfl`, and 20,000 | checks | checks |
| `p2.sw`: the same at 300,000 | `E-RESOURCE`, "recursed more deeply than allowed", while unfolding `inc` | checks |
| `p3.sw`: the same at 3,000,000 | `E-RESOURCE`, depth, while unfolding `Nat.iterate` | the same error, word for word |
| `w1.sw`: three false `rfl`s over 4,000-deep chains, one through `divFuel` with open numbers | `E-REFL` with computed sides and counterexamples | identical output |
| `g1.sw`: open goal, `omega`, `ring`, `/ 2` on an open number, `leq` hypothesis, `Nat.iterateCong 4000` | | identical output |
| `lz.sw`: `mul`, `divFuel`, `leq`, `sub` with a stuck or open first argument and a 3,000-deep second | | identical goals and "computes to" lines |
| `docs/reviews/repros/fuzz-elab-*.sw` (4 files) | | identical once main's `W-ARROW-FORALL` blocks are removed |

`lz.sw` confirms laziness is kept: `mul (stuckOn y) (chain)` takes 674
steps on main and 680 on the lane, so the chain is not forced; `divFuel`
with stuck fuel is 210,887 against 213,889 (the chain is forced by
something else on both).

I could not write a diverging second argument (`leq 0 loop`) in the total
fragment; the argument above (same set forced) and `lz.sw` stand in for
it.

## Findings

### M1 (Medium, accept and record): step counts change in both directions, and small-budget attempts can see them

- value.rs:1395, 2704: each pre-forced argument costs one extra machine
  step (the `Control::NativeArg` iteration). Measured with
  `STITCHWORT_TIMINGS=decls` on `p1.sw`: `deep2k` 152,233 → 154,232 steps
  (+1,999, one per level); `ringy` in `g1.sw` 1,007,027 → 1,019,038.
- unify.rs:3357: a node zonk skips past depth 32 no longer takes its
  step, so zonking takes fewer.

Steps decide outcomes wherever something is tried under a small budget
and "ran out" is taken as "no": `cheaply` (unify.rs:3050, 100,000 steps;
its doc says whether it folds "shows in the elaborated term"),
`unfolding_limits` (unify.rs:3173), omega's and ring's atom comparisons
(20,000 steps), `search::ATTEMPT` (200,000), `assume::side_limits`,
`pretty::stuck_on_goal`. A computation sitting within a few steps of one
of these limits could flip, and with it an elaborated term or a message.
The lane's "results, messages, hashes and proofs unchanged" is therefore
a statement about the corpus it ran, not a property of the change. I
found no flip in any probe, and every step-count change in this repo
carries the same exposure, so I don't think it should hold the merge: the
verifier's hash snapshots and Overmind's rolling check are the right
detectors. Worth one line on the ticket so the claim isn't read as a
guarantee.

If Matt wants the evaluator half strictly step-neutral, the extra step
can go: have `from_native` reach the stack (it is only called from the
machine loop and `resume`) and push `Frame::NativeArg` directly, returning
`Control::Force(arg)` with no `Control::NativeArg` state. Not needed for
correctness.

### M2 (Medium, accept and record): a deep chain's frames now count against one frame limit, three per level

- value.rs:1470 (`push`) with budget.rs:839 (`frames`): the limit is on
  one machine's stack length. Before, each nested machine started from
  zero, so a chain through natives never came near it and was bounded by
  the Rust stack instead (about 8.5 KiB a level). Now the whole chain is
  on one stack. Measured: a 2,000-deep chain peaks at 6,001 frames (was
  2,003), 4,000-deep at 12,003, so three frames a level.
- Under the default limits (2,000,000 frames) this is a large gain: the
  depth that checks goes from under 300,000 (`p2.sw` fails on main) to
  about 666,000.
- Under the 10,000-frame attempts (the list in M1) it is a new cut-off at
  about 3,333 levels. A chain between there and the old Rust-stack bound
  that also fits the attempt's steps used to get an answer and now gets
  "no". The window is narrow (at the 77 steps a level measured for
  `inc`, a 100,000-step attempt runs out of steps at about 1,300 levels,
  before frames matter; only the 1,000,000-step attempts, omega's
  unknown-atom unification and `assume::side_limits`, can reach it), and I
  did not manage to hit it from source.
- This is the direction `Budget::attempt`'s own doc asks for (frames are
  "the same in every build"; stack bytes aren't), so I'd call the new
  behaviour the intended one. The edge to know about: an outer machine
  already deep in frames plus a deep forced chain now share the limit.

### L1 (Low): core.md says nothing about this, and could say one sentence

docs/core.md's "Glued calls" bullet (line 267) doesn't describe how
natives force arguments, so nothing there is now wrong, and reduction is
unchanged as the lane says. But what the kernel accepts did move at the
resource edge (`p2.sw`), and D3210 asks for the spec to follow "what the
kernel accepts". One sentence would do: a native's glued arguments are
forced by the machine that runs it, so a chain of them costs frames
(`Limits::frames`), not Rust stack. The orchestrator's call whether that
is this lane or a follow-up.

### L2 (Low): the new evaluator test covers one shape

`natives_force_a_deep_chain_of_glued_calls_in_one_machine`
(crates/core/tests/it/glue.rs:207) covers `add` with the call in
argument 0. It passes only because the chain no longer recurses (100,000
levels would overflow the test thread), which is a fair check, but it
doesn't assert the claim in its name (the test-only `RUNS` counter could)
and nothing pins the stopping rule. Suggested follow-up tests, all cheap
with the same harness:

- `mul stuck (call)` and `divFuel stuck (call) (call)`: the second
  argument's unfolding cell is still empty afterwards (the laziness
  SW-2572 and SW-3055 rely on; `lz.sw` shows it holds today).
- a call in argument 1 with a number in argument 0, and a three-argument
  native with calls in all three (`next` stepping).
- an argument whose kept unfolding doesn't fit (taken-back metavariable
  epoch): forced again, same value.

### L3 (Low): the zonk test doesn't cover `empty_row_done` past depth 32

`zonk_goes_down_a_deep_term_only_where_it_changes` (unify.rs, tests)
covers a metavariable at depth 100 and sharing of an untouched deep part.
A `doneIn Empty v` below depth 32 with no metavariable near it is the
other way a node gets marked, and has no test.

### L4 (Low): the scan is not budgeted

`Changing::of` (unify.rs:3146) walks the whole subtree below depth 32
without `budget.step()`, so it can't be cancelled or hit a deadline
mid-scan. It is one cheap pass per subtree (the size limit bounds a
read-back at 2,000,000 nodes), so this is a note, not a problem.

### L5 (Low): cost outside proofs wasn't measured

`unforced_number_arg` now runs before every native call, including in
`stitchwort test` and `run --reference`, where no call is ever glued. The
lane measured two proof namespaces (+0.2% and +0.8% instructions). A
test-heavy namespace would show whether the strict evaluator pays
anything; that measurement belongs to the verifier or Overmind, not a
lane.

## Must fix before merge

None.

## Suggested follow-up tickets

1. Tests for the stopping rule and the other argument positions (L2), and
   for `empty_row_done` below depth 32 (L3). Sonnet or DeepSeek.
2. One sentence in docs/core.md on natives forcing in the machine (L1),
   if not added at merge.
3. Record on SW-3132 that step and frame counts changed (M1, M2), with
   the measured numbers, so "hashes unchanged" reads as "on the corpus".

## Tests run

- `cargo nextest run -p stitchwort-core -E 'package(stitchwort-core) & (test(natives_force_a_deep_chain) | test(natives_never_glue) | …)'`:
  2 run, 2 passed.
- `cargo nextest run -p stitchwort-elab -E 'package(stitchwort-elab) & test(zonk_goes_down_a_deep_term)'`:
  1 run, 1 passed.
- Probes as in the table above, one `check --no-cache` at a time under
  `nice -n 19`.

Not run: any suite, whole-AoC check, Day22.Proofs itself, the playground
(WebAssembly) build, or a base-commit binary (main's stood in for it).
