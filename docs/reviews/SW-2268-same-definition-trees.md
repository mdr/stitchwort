# SW-2268: review of SW-2256 (same-definition stuck calls by their trees)

Reviewed 7 Nov 2026, read-only, against `36bb2f3a0` (merged in `3da301476`).
Scope: `crates/core/src/value.rs` (`conv_step`), `crates/core/src/reference.rs`
(`conv_in`), `crates/elab/src/unify.rs` (`unify_step`), `docs/core.md` rule C
and the gaps table.

## Summary

The change is sound. Everything it newly accepts is delta plus case
congruence: both calls unfold to their residual trees, which are compared
node by node exactly as two different definitions' already were. Nothing
false gets in. The three sites agree on everything except calls whose
arguments may mention an unknown, where the unifier keeps its old
arguments-only rule (filed as SW-2267). Termination holds: `opens_by_tree`
excludes recursive definitions, every loop takes a budget step, and every
error is propagated with `?`, so an overrun is `E-RESOURCE`, never
"different". Two things are worth a lane:

1. The argument try runs in the current mode, which leaves an existing
   transitivity break with proof fields in place (F1).
2. A failed argument try is redone by the tree try, so the cost of nested
   stuck calls of one definition grows exponentially with depth (F2).

Top recommendations:

1. Run the argument try in shortcut mode at all three sites (F1).
2. Remember pairs of trees found different in each outermost comparison, as
   `TreeMemo` remembers equal ones (F2).
3. Add a test for G11 (F3).
4. Correct the wording of rule C in `core.md` (F4).
5. Keep the unifier's undo (F5). It is correct, but today nothing reaches
   it.

Counts: high 0, medium 2, low 3.

| # | Severity | Confidence | Where | Finding | Size |
|---|---|---|---|---|---|
| F1 | medium | medium | value.rs:3381-3405, reference.rs:851, unify.rs:1609 | The argument try uses the current mode, so proof fields are skipped. Calls can then be called equal although their trees differ, which breaks transitivity. This predates the change but is still there. | S-M |
| F2 | medium | high | value.rs:3381-3408 (and the same in the other two sites) | A failed argument try is redone by the tree try, so nested stuck calls of one definition cost 2^depth on failure. | M |
| F3 | low | high | proof_equivalence.rs | The commit says G11 is fixed, but no test covers it. | S |
| F4 | low | high | core.md:255 | Rule C says the argument shortcut runs "in shortcut mode", and that the unifier "keeps what they solve". Neither is quite what the code does. | S |
| F5 | low | high | unify.rs:1609-1630 | Both undos are correct. They are unreachable today, because the arm only runs when neither spine mentions an unknown. | none |

## Details

### F1: the argument try in normal mode (lane doubt 1)

`Mode`'s doc (value.rs:3035-3049) says the shortcut mode is for every place
that answers "equal" for two calls of one definition from their arguments
while the calls could still unfold. Before SW-2256, a stuck call counted as
rigid here. Its spine was compared in its own mode (see the comment at
reference.rs:886-890, "A stuck call's isn't"), and then "different" really
meant different. Rule C now treats a stuck call's head as its residual tree,
so the stuck call is exactly what the `Mode` doc describes: something that
answers "equal" from arguments while the comparison could still look
inside. A concrete triangle, with `P : Prop`, `p q : P` and `Box` a structure
with one proof field:

```
def f (b: Box P) (x: Bool): P := match x | True => (match b | MkBox r => r) | False => …
def g (r: P) (x: Bool): P    := match x | True => r | False => …
```

- `f (MkBox p) x ≡ f (MkBox q) x`, by the argument try in normal mode: the
  proof field is skipped.
- `f (MkBox p) x ≡ g p x`, by the trees: `MkBox p` is a constructor, so
  `walk_tree` takes its branch, and the leaves are `p` and `p`.
- `g p x` against `f (MkBox q) x` compares the leaves `p` and `q`. Two
  variables are "different", unless conversion identifies all proofs, which
  I don't think it does for neutrals. That is the open question behind the
  medium confidence.

It isn't stable under substitution either: with `x := True`, the first pair
becomes `p` against `q`. This isn't unsound, because every pair here proves
the same proposition. But it is a G6-shaped break of transitivity that
SW-2256 leaves in place, and the change did not cause it.

Shortcut mode for the try loses nothing that matters. When the arguments
differ only in a proof field, the tree try still finds the calls equal
whenever the tree never reads that field. It also lets the argument try hit
`CallMemo`'s `Differ::Values` entries, which `same_spines` records under
`Mode::Shortcut`. That speeds up glued arguments (F2).

Recommendation: at all three sites, use `Mode::Shortcut` for the argument
try only: `same_spines` in value.rs, `conv_spines(…, Mode::Shortcut)` in
reference.rs, and `Mode::Shortcut` in the `run` in unify.rs. The tree try
keeps `mode`. Add the triangle above, as a probe first, to
`proof_equivalence.rs`'s transitivity tests. Confirm with that probe before
changing anything, since it rests on how proofs are compared at the leaves.

### F2: repeated work on failure (lane doubt 2)

Take `pred (pred (… a))` against `pred (pred (… b))`, `n` deep, where `pred`
is a non-recursive `match` (or `tail`, or `xs.tail.tail.tail`):

1. The argument try compares the inner pair, which in turn runs its own
   argument try and tree try, and fails.
2. The outer tree try then reaches a `case` stuck on that same inner pair as
   its scrutinee, and compares the pair again.

So T(n) = 2·T(n-1), where before the change it was linear and answered
"different" at once. At about 25 levels a failed comparison becomes
`E-RESOURCE` instead of a type mismatch. Failed comparisons are routine in
the unifier (alternatives, instance search), so this is a cost and
error-quality risk, not a correctness one.

Lane doubt 2 asked whether skipping `CallMemo` is a correctness issue. It
isn't, and it can't be, because `CallMemo` is keyed by the addresses of
`Value::Call` unfolding cells. A forced stuck call is a `Neutral`, which has
no such key. Recording "different" in a memo is valid in the kernel, where
there are no metavariables and the answer depends only on the values, the
level and the mode. It would also be valid in this unifier arm, which only
sees spines with no unknown in them, and under `TreeMemo`'s `meta_epoch`
rule. Glued arguments are partly covered already: the inner `Call` pair
records `Differ::Arguments`, so its argument shortcut isn't retried, but its
unfolding is.

Recommendation: let `TreeMemo` remember "different" as well as "equal":
`record_different` when `same_stuck_trees` returns `false`, keyed and looked
up as now, and dropped on a new `meta_epoch` in the unifier. Also check it
before the argument try. Add a test that a pair of `pred`s about 30 deep with
different bases answers "different" within a small budget, in all three
modes.

### F3: G11 has no test

The commit and the ticket say that G11 (`needSame [a := 1] x rfl`, from
`docs/reviews/SW-2251-equality-rule.md:217-241`) is fixed, but no test or
probe contains `needSame`. Add an elaborator-level accept test, next to
`docs/repros/sw-2236/g6.sw` or in `proof_equivalence.rs`.

### F4: core.md rule C

- The list of shortcuts says "two calls of one definition (glued, folded or
  stuck) with arguments equal in shortcut mode". For stuck calls that open
  by tree, the code compares the arguments in the current mode. Fixing F1
  makes the text right. Otherwise the text needs changing.
- "The unifier tries the arguments first, keeps what they solve if they
  match" suggests the try solves unknowns. In this arm it can't (F5). The
  arguments-may-mention-an-unknown case is the next clause. Suggested text:
  "where neither side's arguments mention an unknown, the unifier compares
  them, and if they differ, the trees, as `conv` does; where they may
  mention one, it still unifies them alone, in shortcut mode (SW-2267)."
- G11 isn't in the gaps table. Either add it as a row marked fixed, or
  mention it in G6's row.

### F5: the unifier's undo (brief question 4)

The arm runs only after the `blocked` and `may_mention_meta` arms have
declined (unify.rs:1590-1603), so both spines are free of unknowns, solved or
not. (`may_mention_meta` answers `false` only after it has looked at every
part.) Definition bodies outside the pending group contain no unknowns
either. So neither the argument try nor the tree try can solve anything, and
`undo_since` has nothing to take back.

If that ever changes, the structure is right:

- The trail is taken once.
- If the argument try fails, everything since the trail is undone before
  the tree try starts, so nothing solved by the argument try can leak into
  the tree try or out of the arm.
- If the tree try also fails, it is undone again.
- `nested` clears `waiting`, so no pair can be postponed half-done.
- `undo_since` also calls `forget_lossy_since`, and bumps the epoch through
  `metas_taken_back`, which invalidates `TreeMemo`.

One side effect does survive a failed try: `record_different` entries in
the call memo. These are facts about values with no unknowns in them, so
they stay true.

Keep the undo. It is cheap, and it makes the arm safe if the guard is ever
loosened (SW-2267).

## Checked and sound

- **Newly accepted equalities are definitional (Q1).** The new path is
  delta plus case congruence, through the same `same_stuck_trees` used for
  two different definitions. `walk_tree` takes constructor branches as
  evaluation does, and only compares `case`s stuck on neutrals. A
  `NumCase`, a number or a range, or a leaf against a `case` still answers
  "different" (G3, G7 and G8 are untouched). The rule for impossible
  `case`s still keeps inert arguments from affecting the answer.
- **The sites agree on when the rule applies.** Each needs both sides to
  open by tree, and `opens_by_tree` requires a fully applied spine of
  applications only, so the spines have equal lengths and `spine_pairs`
  never returns `None` here. The `None => false` in value.rs is dead but
  harmless. All three skip inert arguments in the same way (`spine_pairs`
  and `conv_spines`). `sealed` and folded definitions are handled before
  these arms and are excluded by `opens_by_tree` anyway. All three pass the
  same `mode` to both tries.
- **Termination and budget (Q2).** The definitions aren't recursive, so
  each tree opening goes down the definition order, and nesting is bounded
  by the data. Every loop (`conv_with`, `walk_tree`, `run`, the reference's
  recursion) takes `budget.step()?`, and the Rust-stack recursion goes
  through the stack guard. No `Err` is turned into `false`: the argument
  try and the tree try both propagate with `?`. F2 is a cost, not a
  correctness issue.
- **The unifier's undo (Q4).** Correct; see F5.
- **The tests.** The two tests turned on (`probe_g6_same_definition_stuck_calls`
  and `the_relation_is_transitive_over_an_unused_argument`) do test G6's
  triangle.
- **The 1 Nov codebase review** (`docs/research/rust-codebase-review.md`)
  has no findings on `same_stuck_trees`, `CallMemo`, `TreeMemo` or
  `opens_by_tree`, so none are in scope.

## Tickets to file

- **Lane A (Opus, 45-60 min; kernel conversion, so D2364 applies):** F1
  and F4.
  1. Probe the proof-field triangle in all modes.
  2. If it shows the break, switch the argument try to shortcut mode at all
     three sites, and add the test.
  3. Correct rule C and add G11 to the gaps table.
- **Lane B (Opus or Sonnet, 45-60 min):** F2. Have `TreeMemo` remember
  pairs found different, add the `pred`-chain cost test in all three
  modes, and check that the unifier forgets those entries at a new epoch.
  It can follow lane A or go together with it, since it touches the same
  arms.
- **Lane C (Sonnet or DeepSeek, 15 min):** F3, a G11 accept test.
- SW-2267 (unknowns in the arguments, in the unifier) already covers the
  one place where the sites disagree.

## Calls I made

- I treat F1 as pre-existing rather than as a regression from SW-2256, and
  I didn't raise it as a D question: the fix stays within rule C as
  written. It needs a probe first.
- No D questions.
