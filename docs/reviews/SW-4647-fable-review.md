# SW-4647 review (Fable): kernel conversion remembers pairs of calls found equal

Reviewed: `git diff main...lane/SW-4647`, commit 9f57c14cf, read-only. Line numbers are of
`crates/core/src/value.rs` at that commit unless another file is named. Nothing was built or run.

## Verdict

**Merge with one change: a test that provably hits the new record.** No soundness problem found.
The remembered "equal" is the answer recomputation gives, for the reasons below; what is missing is
evidence that any checked-in test ever reads a `Found::Equal` entry.

## 1. Soundness: no finding

The claim to check is that `conv_with`'s answer for a pair of glued calls is a function of
(mode, level, the two values, the fixed environment) only, so that a remembered answer equals a
recomputed one. It is.

- **Timing, nothing left pending.** `Found::Equal` is recorded at 4496, after `same_spines`
  returned `true`. `same_spines` (4107-4131) compares each argument pair with its own
  `conv_with` call, run to the end of its own work list (3945-3981), and pushes nothing onto the
  caller's work list. So the "equal" owes nothing to work still queued, unlike most
  `Step::Answer(true)` returns in `conv_step`, which mean "equal if the pushed parts are". The
  lookup's `Step::Answer(true)` (4210) also pushes nothing, the same as the computed path.
- **No in-progress assumptions.** Neither memo assumes a pair equal while it is open. `CallMemo`
  records only after the comparison; the tree memo records after `same_trees_of_calls` returns
  (4912-4925) and its lookup only reads finished pairs (5176-5200). No coinductive or cycle
  hypothesis exists in `conv`, so no circular "equal" can be baked in.
- **Mode.** Arguments are always compared in `Mode::Shortcut` (4125), whatever the caller's mode,
  so "equal by arguments" is in fact the same in both modes. The key carries the mode anyway
  (4062, 4496), which is conservative.
- **Proof positions.** A skipped proof is never compared, so nothing is recorded for it. Inert
  arguments are left out by `spine_pairs` in both modes (4631-4633), by position in the
  definition, not by where the call sits. An entry made anywhere is therefore the answer
  anywhere. The homogeneity precondition of `conv` (3900-3911) governs whether an answer is
  meaningful, not what it is: an untyped recomputation at the second site would return the same
  boolean, so the record cannot make things worse than the tree walk.
- **Binders and levels.** Values use de Bruijn levels and `conv` reads no typing context; the
  level only chooses fresh variables (4317, 4000). It is in the key.
- **Eta.** Function and record eta act on lambdas, neutrals and constructors, after calls are
  forced (4428-4470); the `Calls` rule runs before them and doesn't depend on them.
- **Unknowns.** `conv` is also called by the elaborator (for example
  `crates/elab/src/check.rs:878`), where values can hold metavariables. `conv` solves none and
  nothing it calls unifies (comment at 5049-5054), and the record is a local of one `conv` call
  (3913), so no solution can change under a live entry. In the kernel there are none.
- **State that changes during a comparison.** Unfolding cells are filled by `force`, the tree
  memo and `Unread` grow; all are caches of the same function. Errors (budget, stack) propagate
  by `?` before the `record` at 4496, so no entry follows a failed comparison.
- **Other entries.** `Found::Different` (4126) and `ArgumentsDiffer` (4499) are unchanged in
  meaning. An entry can't flip: `Equal` and `Different` for one key would need two different
  answers from the same deterministic comparison.

## 2. Key identity and scope: no finding

- Key: `(mode, level, address of a's unfolding cell, address of b's)` (4062, 4076-4086), only for
  two calls of one definition. The entry holds clones of both values (4095), which hold the
  `Rc<Unfolding>`s, so an address can't be reused while the entry lives.
- One cell, one call: every construction of `Value::Call` makes a fresh cell (`Rc::default()` at
  1645, 2813, 3733; `crates/elab/src/unify.rs:2338`, `2919`; `matching/untouched.rs:129`), or
  keeps the cell with its own spine. The one that changes a spine, `project_call` (2543-2552),
  allocates a new cell whose `base` is the old one. `force_call` rebuilds the base call from
  `unfolding.base` with the spine minus the projection (1405-1409), which is that cell's own
  call. So two calls with different definitions or arguments never share a cell.
- Ordered: `(a, b)` and `(b, a)` are different keys. A miss, never a wrong answer.
- Scope: a fresh `CallMemo` per outermost `conv` (3913), dropped when it returns. Not
  thread-local (unlike `TREE_MEMO`, 5110), so nothing passes between comparisons, declarations,
  or the kernel and the elaborator.
- Determinism of counters: hits depend on which cells are shared, not on address values, and
  lookups are point lookups, so step counts stay reproducible (unlike SW-4648's address-keyed
  `dot_heads`).

## 3. Memory: low

The record is not bounded within one comparison and is cleared only when the outermost `conv`
ends. It gains one entry per distinct pair of same-definition calls found equal, where before only
differing pairs were kept; each entry is the key plus two `Value` clones. The count is bounded by
the step budget (each `Recursion::Calls` follows a `budget.step()` at 3955). The values held are
mostly already alive through the roots, since cells keep their unfoldings. For the measured
example the distinct pairs are at most a few hundred thousand (7.3M steps in all), where the tree
walk met 4.3M. Not measured: peak memory before and after. Worst case is a long comparison of
many distinct equal pairs, at roughly 100 bytes each; I'd accept that.

## 4. docs/core.md: accurate, two small gaps

- The glued-calls sentence (`docs/core.md:267`) says what the change does and that it is within
  one comparison. It doesn't say the record is by mode and level; line 276 says `CallMemo` is
  keyed by the mode. Suggest adding "at the same level" there. Minor.
- Pre-existing, not from this lane: Rule C (`docs/core.md:331`) lists `CallMemo` among the
  shortcuts "which answer 'equal' or nothing, never 'different'", and
  `crates/driver/tests/proofs/conv_shortcut.rs:11` says "The shortcuts can only answer 'equal'".
  `CallMemo` has answered "different" from its record since D483 (4211), a remembered Rule C
  answer. Worth one sentence in both places now that the paragraph was touched. Minor.

## 5. Test coverage: the gap (medium)

`conv_shortcut` compares verdicts with and without the shortcuts over `examples/reject` and
`examples/soundness` only (`conv_shortcut.rs:48-66`). The switch does turn this shortcut off
(4207), so the test would catch a wrong hit in an example that has one. But nothing shows any of
those examples reads a `Found::Equal` entry: a hit needs the same two cells compared twice in one
`conv`, and the lane's own attempts at a small reproducer failed (performance log entry). The
ticket's `accepted_examples_check` runs don't compare with and without. So the only known
exercise of the new path is the `tools/fmt` check, which no with/without test covers.

Failure this leaves open: a later change that breaks the invariant (a `Value::Call` built with a
shared cell and another spine, say, or a record made before the arguments finish) would wrongly
accept, and no test would see it.

Asked for before merge, either of:
- a unit test in `value.rs`'s tests with `conv_both` (6109-6120), which already asserts the two
  answers agree and returns both step counts: two towers of calls, each level `f c c` with one
  shared cell per level, built separately so the sides aren't identical; assert equal, and that
  the steps with the shortcut are linear in the depth (so the record was read). A second pair
  differing at the bottom would cover "different" beside it.
- or evidence that a named reject or soundness example hits the record (its step count differs
  between main's binary and the lane's), named in `conv_shortcut.rs`'s header as
  `case-tree-chains-*` is for the tree memo.

## Optional

- "Equal by arguments" and "arguments differ" don't depend on the mode (arguments are always
  compared in shortcut mode), so those two could be looked up under either mode; only
  `Different` needs the mode. A possible further saving, not needed.

## Not settled

- Whether any existing reject or soundness example hits the record (needs a step-count
  comparison of two binaries, or a counter).
- Peak memory of the two `tools/fmt` examples before and after.
- I didn't re-measure the reported timings.
