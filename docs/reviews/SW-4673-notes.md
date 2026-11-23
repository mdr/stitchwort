# SW-4673: rules K and S (full proof irrelevance, stage 4): notes for review

Opus lane, 23 November 2026, for the Fable review. Decisions: D3721 (end state E2), D3723
(work towards it), D3724 (a user's one-constructor indexed proposition computes like `=`, as
Lean's `to_cnstr_when_K`: no fields beyond the parameters, indices compared). Design note:
docs/proposals/full-proof-irrelevance.md §3, §4.4, §5, §9; audit conditions A, B and G:
docs/proposals/full-proof-irrelevance-audit.md. Spec: docs/core.md, "Rules K and S".

## What changed

| Where | Change |
|---|---|
| `term.rs` | `Term::j_ends`: a cast's ends are read off its proof, `Ann(p, Eq(Some(A), x, y))`. No new term field: the annotation *is* the carrying (§"Why an annotation") |
| `check.rs` `infer_j` | for a `J` whose result mark is `NotProof`, wraps the proof in its equation, quoted with calls kept (`quote_kept`); a proof already annotated with a filled-in equation keeps it |
| `check.rs` `infer_proj` | also accepts `Proj` of a proposition with one constructor, no indices and only proof fields: rule S's stand-in reads back as such a projection, so a read-back term holding one checks |
| `termination.rs` | doesn't walk a cast's ends (only the proof inside the annotation) |
| `value.rs` | `Ends`, `Elim::J.ends`; rule K at `Frame::JForced` and again at `ReplayElim`; `ends_meet` / `meet_in_evaluation` (reserved levels); quote writes the ends back; `conv_step` compares two stuck casts by parts (finding B); `fire_cast` for the unifier; rule S in `branch` (`one_shape`, `parameter_type`) |
| `machine.rs` | `cast_levels`: levels in use by evaluation-started comparisons |
| `reference.rs` | the same rules written separately: K in `eval` and `apply_spine`, `ends_equal` with its own thread-local depth, quote, finding B in `conv_in`, `rule_s` in `eval_tree` (which now takes the definition) |
| `elab/unify.rs` | `fire_cast` before comparing, finding B for two stuck casts, `rename_spine` keeps ends |
| `proof_counts.rs` | `CastFired`, `OneShapeFired` |

## Why an annotation, not a new field

`J(P, d, p)` gains its ends as `J(P, d, (p : x = y))`. An annotation already means "this term,
at this type"; its type here is exactly the proof's type, so nothing about `p`'s meaning
changes, every walker already handles `Ann`, the check cache's codec and the term format are
unchanged, and re-checking a checked term is idempotent (the kernel keeps an annotation whose
equation is filled in). What it costs: the convention lives in `Term::j_ends`, and a walker
that should skip the ends (termination) has to know it. Walkers that see them and don't skip:
hashing (wanted: the ends are part of the term), `inert.rs` (walks only `Ann`'s term, so
skips them), the assumption walk (could newly see an assumption mentioned only in a cast's
proof's type; not seen in any test, noted below). Reviewer's call whether this is the end
state or a stepping stone to a fifth field.

The ends are quoted with `quote_kept` (calls kept as calls), against the comment by
`substitute` that says such read-backs never go into checked terms. That rule was there so
hashes didn't move when it was introduced; here hashes move anyway, and the folded form is
convertible to the unfolded one and much smaller (F1 of the SW-4671 review: never write out
a huge value). Deterministic for a given term, so the hash is stable.

## Soundness: the model argument

The model is the one D1′ rests on: every proposition has at most one element (Carneiro §6).

- **K.** A proof of `x = y` exists only if `x` and `y` are the same element; then `J P d p`
  is `d`. The rule fires only when `x ≡ y` already, so it adds `J P d p ≡ d` exactly where
  the model has it, for any `p`.
- **S without indices.** `E-PROP-ELIM` admits a proposition into data only with one
  constructor, all fields proofs, not self-referential, alone in its group. Its one element
  is the constructor applied to its fields, so the branch with the fields bound to "field `k`
  of the proof" is that element's branch. The stand-ins are projections, proofs themselves.
- **S with indices, no fields.** The one constructor's value has the indices `r(ps)`; a proof
  of `D ps is` exists only if `is = r(ps)`. The rule fires only when `is ≡ r(ps)`, where the
  branch's refinement (the index unification the kernel did when checking it) already
  holds, so the branch is evaluated in a context of the type it was checked at.
- **Two stuck casts by parts.** Two casts with equal ends' type, ends, motive and base are
  both `d` transported along a proof of the same `x = y`; in the model the proofs are equal,
  so the casts are. Comparing the element types first makes every later pair homogeneous
  (finding B's requirement).
- **New `Proj` typing.** `Proj(D, i, t)` for a proof record `D` gives a proof of field `i`'s
  proposition: proof out of proof, which `E-PROP-ELIM` would allow by a `case` anyway.

## Subject reduction

- A K step takes `J P d p : P y p` to `d : P x byComputing`. `x ≡ y` is the rule's condition.
  `p` against `byComputing` is equal only at D1′'s proof positions; a motive whose body
  computes with its proof argument (rare: a data type indexed by a proof) still separates
  them. This is the gap October's §5.7 describes, not a new one; rule I (stage 5) closes it.
- An S step is a `case` that takes its branch: the branch was checked with the fields bound
  and the refinement applied; the stand-ins have the fields' types (projections of the
  scrutinee), and the index test makes the refinement hold.

## Termination, and the Abel-Coquand program

- **No new loop from K into data.** A fired cast is replaced by its base, which has the
  same type up to the ends (equal); a fired `case` removes a `case`. Neither adds a step that
  can repeat. Data-level termination stays what it is today: assumed, argued.
- **The ends test can itself evaluate.** It calls `conv`, which may unfold calls in the ends
  and meet further casts; each is a smaller sub-problem of the current comparison, and the
  shared budget bounds it (`E-RESOURCE`, never "different"). In principle only: the Fable
  review's F1 found ends that each hold the same recursive call doubling the work per level
  (100 s and more at 41 levels). Fixed on this branch by remembering answers for the rest of
  the outermost test (`Machine::cast_answers`) and evaluating the ends glued; 41 levels now
  take 0.5 s and 161 levels 10 s (polynomial: each cast evaluated outside a test starts a
  new outermost one). A lazy cast, tested only where its head is needed, was tried and set
  aside: number matches and stuck-tree comparisons read heads without it, and the test of
  record found them (`scratchpad` patch, not committed).
- **Abel-Coquand** (`examples/accept/abel-coquand.sw`): still checks, unchanged, with no
  budget hit. Every `J` in it is `J (y e => y) …` with `y: Prop`, so its result is a proof,
  its mark `Proof`, it carries no ends, and rule K doesn't apply; it stays stuck on `h Top
  a` as before. A data-producing version of the loop would need a cast whose element type is
  `Prop` and whose result is data, but the motive's result *is* the element, a proof. The note's
  prediction (§5.3) holds: the checker never computes inside the proof.

## Condition A: fresh variables

`conv` makes fresh variables from its `level`, which must be above every free variable of
the two sides. Evaluation has no level. `ends_meet` (and rule S's index test) compare at
`RESERVED_LEVELS = 2^40` plus `cast_levels`, which each test in progress raises by `2^24` and
restores on exit (also on error: a `Drop` guard). A test nested inside another's comparison
(a cast met while unfolding the outer ends) starts above the outer one's whole range, so the
outer's fresh variables, which may be free in the inner ends, are never reused. Contexts never
reach `2^40` (they are bounded by the program and the budget). The reference evaluator does
the same with its own thread-local depth.

Tests: `rule_k::the_ends_test_makes_its_own_fresh_variables` (core unit test: with six
variables in scope, `z => z` and `z => v5` compared at level 5 are "equal", and `ends_meet`
says different); `soundness/proof-irrelevance-31-cast-ends-fresh-variables.sw`.

## Condition B: stuck casts compared by parts

`cast_at(spine)` finds the first `J` carrying ends; everything before it is the proof. Two
neutral values both with one are compared by ends' type, ends, motive, base, then the rest of
the spines; the heads and the proof elims never. `value::conv_step`, `reference::conv_in` and
the unifier each have this arm, ahead of the same-head arm. A stuck `case` on a proof (one
that rule S didn't fire) is still compared through `same_trees_of` as before; the audit's
suggestion to skip a proposition's scrutinee there is stage 5's, since it matters only once
rule I removes the step its precondition rests on.

Tests: `accept/rules-k-and-s.sw` `sameEnds` (equal), `soundness/-32` (different ends).

## Condition G: undo

- The K test is `conv`: it solves nothing and writes no trail.
- A cast stuck on an unknown in its ends: evaluation leaves it stuck with its ends. The
  unifier calls `fire_cast` on each side before comparing; if the ends meet *now* it compares
  the base with the rest of the spine applied. The result isn't written back into any value.
  A metavariable's spine replayed after its solution (`ReplayElim`) tests again, but that
  replay is itself the forcing of a solution, so it lives as long as that solution's forced
  values do, which kept unfoldings already tie to `meta_epoch`.
- What I did not trace: whether a glued call's kept unfolding computed in an attempt that
  fired a cast because of a solution, later taken back, is dropped. It's the same mechanism as
  any other computation through a solution, which the epoch handles; no new cache was added.

## The reference evaluator's independence

`reference.rs` implements K (`eval` of `Term::J`, `apply_spine`), S (`rule_s`, reading the
parameter's type from the definition's `Term` type and evaluating it with the reference
`eval`), the read-back of ends and finding B with its own code. It calls nothing in
`value.rs` that evaluates: the shared pieces are the data types, `Term::j_ends` (syntax) and
`Ends` (a struct). Its fresh-variable range uses the same constants but its own counter.

## What's accepted now that wasn't

- Accept examples moved from reject or soundness: `omega-basics`' `transportComputes`,
  `sealed-theorem-cast`, `quot-transport-ind-rule-k` (was `reject/quot-transport-ind-stuck`),
  soundness `-05`, `-17`, `-18`, `-21`, `-27` (the note's list predicted `-05`, `-17`, `-21`; `-18`
  and `-27` are one-shape matches too, also in the note's §6.1 list).
- `reject/mismatch-hidden-proof-argument` and `refl-hidden-proof-argument` tested the SW-28
  message with a definition that casts along its proof; that is now equal by K and B. They
  use a function variable instead, which might still compute with its proof.
- e2-only.sw probe 8 (`atOne`) now checks too: its `J` is along `h: 0 = 0`, ends `0` and `0`.
- Nothing that checked before is refused, as far as the tests run here show (see "Not
  checked").

## Not checked

- Whole std, `aoc/`, `games/rogue`, `tools/fmt`, the full examples suite (verifier and
  Overmind). Only the soundness set, the touched examples, and a scan of reject examples whose
  text mentions casts (I started a scan of all reject examples and stopped it as outside the
  lane's budget).
- Whether an assumption mentioned only in a cast's proof's type now counts as relied on (the
  ends are walked by the assumption walk).
- `quote_kept` ends on terms that are later re-checked by the reference validator: passed in
  the tests run, not looked at further.
- The unifier's `first_order` (finding D) and searches (finding E): stage 5.
