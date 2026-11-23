# SW-4674: rules I and F (full proof irrelevance, stage 5): notes for review

Stage 5 of docs/proposals/full-proof-irrelevance.md, with the audit's
conditions (docs/proposals/full-proof-irrelevance-audit.md) and the open
items of the SW-4671 and SW-4673 reviews. The rules as built are in
docs/core.md, "Proof irrelevance" (the four rules and where each lives) and
"Proof marks".

## What changed

- **Rule I.** Two values both marked proofs are equal, unlooked at:
  `value::by_rule_i` (the kernel's `conv`, first thing for each pair),
  `reference::conv` written apart, and the unifier's `by_rule_i`, which
  still solves a side that is itself an unknown with the other and solves
  nothing inside.
- **Rule F.** `value::frozen(g, id) = def.proof && !program_running`: a
  proof-valued definition's call, a `J` into a proposition and a `case` in a
  proof's tree never unfold while checking. Read wherever `body_seen` is, so
  a frozen call is `sealed`: compared by its arguments, which rule I answers
  for the proofs among them.
- **Deleted:** the shortcut mode (the second comparison mode that compared
  proof fields inside equal-only shortcuts, its `CallMemo` and tree-memo
  key), the inert analysis (`inert.rs`, `Def::inert_params`,
  `reference::validate_inert`, `tests/elaboration/inert_params.rs`), and
  the cache's copy of the inert marks.
- **The elaborator marks its variables** (`value::mark_of_type`, and
  `Ctx::fresh_var`, `Ctx::last_var`, `bind_hidden`). Without it the
  prelude stopped checking (`Decidable.elimCong`, `elimEq`, `Prop.irrel`):
  rule F freezes a proof's call, and two such calls with proof variables in
  them were compared by those variables, unmarked, so different. Marking
  reads the type: an equation, a data type's sort, a function type's
  codomain under a fresh variable, a stuck head's type applied to its
  arguments; anything else, or an error, is *unknown*, which only costs an
  equality. About 15 sites still make an unmarked variable
  (`omega.rs` 555, 969, 4331; `ring.rs` 1263, 1288; `effects.rs` 3837;
  `auto.rs` 977; `facts.rs` 561, 1008; `bind.rs` 428; and the
  `cod.apply(Value::var(level))` walks): completeness only, none was needed
  by anything that checks. A follow-up can sweep them.
- **Condition D** (unify `first_order`): two proofs pair by rule I only once
  `learn_types` unified their types; otherwise only if they are the same
  value.
- **Condition E** (SW-4661's patch): `matching.rs`'s `same_shifted` is
  `same_in(None, …)`, and `same_shifted_but_proofs` compares two terms with
  proofs equal (a constructor's proof field, a data type's or a
  definition's proof parameter, by `proof_parameter`'s read of the binder
  mark), used by `rewrite.rs`'s `shown_after` and `Search::decide`. The
  `emptyIsByPosition` workaround in `Aoc.Common.Proofs.PrefixSums.atOf` is
  reverted.
- **Cast ends** (SW-4673 review): `identical` compares them, `shape_hash`
  ignores them (coarser, and `identical` decides), and `Unchanged`,
  `value_levels` and `untouched.rs`'s scan walk them. Under `reference` the
  kernel re-derives a given cast's ends from its bare proof's type, where
  that can be inferred, and asserts they agree (`infer_j`).
- **F2-F5** (SW-4671 review): `prop_mark` derives a function type's binder
  mark instead of reading the value's; two known binder marks that differ
  give `NotProof` (`ProofMark::or`); the unknown's mark (`meta_mark`) is
  kept by epoch and trail length and passes errors on; `Refl` against an
  equation of two proofs asserts the equation's type is a proposition under
  `reference` (the tripwire, condition C, in the kernel, alongside
  `by_rule_i`'s panic on a proof against visible data); marks are cleared
  and re-derived on a cache re-check (`Term::without_marks`), and the test
  `proof_masks::cleared_marks_are_derived_again` checks every case's body
  with its marks cleared gives back the same marks.
- **Floats.** `Bool.canonicalTrue` is gone: it existed so a `Float` built by
  a definition and one built by a native held the same proof term, and
  under rule F it no longer computes. `Float.make` keeps the proof it is
  given; the float gate compares normal forms with constructors' proof
  fields written `byComputing`. Every float native's pin moved.
- **Cache** `FORMAT` 40 → 41.

## Soundness of rule I

In the model a proposition has at most one element, so any two proofs of
one proposition denote the same thing; `conv` is only ever asked about two
values of one type (its precondition, now stated on `value::conv`,
`reference::conv` and `unify::unify`), so two values both marked proofs are
two proofs of one proposition. Marks are sound by stage 3's argument (a
mark is a sort the kernel computed; it survives substitution because `f a`
is a proof exactly when `f` is), and the kernel never trusts one it didn't
derive (F5, and now the cache re-check).

## Transitivity without the shortcut mode

The shortcut mode existed because positions were skipped only in the
normal mode: a call's arguments had to be compared with proof fields
looked at, or "equal arguments" could say equal where the unfoldings
differ. Under rule I proofs are equal everywhere, and unfolding never reads
a proof (rule F; rules K and S look only at ends and indices), so equal
arguments give equal unfoldings in every mode, and one mode is enough. The
test of record (`proof_equivalence`) checks reflexivity, symmetry,
transitivity and stability under substitution over its enumerated terms,
now with `p`, `q` and `t` marked as proofs.

## Decidability and termination with rule F

Rule I alone breaks subject reduction (a term accepted at a type can reduce
through a non-`byComputing` proof to one that isn't), and with it the
argument that conversion terminates on well-typed terms. Rule F removes
every reduction that reads a proof during checking, so what is compared
is what was checked. Programs still run proofs' calls (`program_running`),
where nothing is compared.

## Memo keys and marks (F4)

`CallMemo` and the tree memo key by shape, not marks. A remembered "equal"
may now rest on rule I. Two structurally identical calls put a variable in
positions of one type, and a type has one sort, so the same key can't meet
a variable marked a proof in one place and data in the other within one
comparison. A mark that is *unknown* in one and decided in the other only
loses rule I's answer, not soundness: `identical` compares marks.

## Rule S's `E-PROP-ELIM` trust (SW-4673 review)

`one_shape` trusts that `E-PROP-ELIM` already refused a recursive
proposition, or one not alone in its group. Rule I adds no elimination: it
only answers comparisons, so no new path takes data out of a proof, and
rule S's conditions are unchanged.

## Inference gives up (D3725)

An unknown appearing only inside a proof is never solved from it. That was
the only loss across std and the AoC checks run: four `Std.Set.Spec`
lemmas, where `Map.getAlter`'s function argument had been inferred through a
proof; Matt chose writing it out (D3725). `examples/accept/rule-i.sw`
records the probes.

## Examples

Moved soundness → accept, each with a header saying it was refused before
rule I: `proof-irrelevance-04`, `-12`, `-13`, `-19`, `-22`, `-23`, `-24`,
`-25-hidden-call`, `-25-unfolded`, and `quot-ind-computes` (a `Quot.ind`
proof now equal to any other); `reject/char-arm-opaque-call.sw` to accept.
`soundness/index-proof-conflict.sw` now refuses with `E-NOT-EMPTY`.
`proof-irrelevance-15` still refuses, rightly (3 against 4: data, not a
proof).

## Not done here

- The ~15 unmarked elaborator variables above.
- The guide's chapter 10 already said two proofs are interchangeable; no
  newcomer-facing feature changed beyond the inference loss, which the
  proving guide now describes.
