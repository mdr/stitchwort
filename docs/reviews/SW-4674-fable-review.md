# SW-4674 (rules I and F; shortcut mode and inert analysis deleted): Fable review

Reviewed: `lane/SW-4674` at `01f305262` against its merge base with `main`,
23 Nov 2026. Read: the kernel diff in full (`value.rs`, `check.rs`,
`term.rs`, `globals.rs`, `unify_index.rs`, `reference.rs`'s `conv`), the
lane's notes, `docs/core.md` "Proof irrelevance" and "Proof marks", the
unifier's `by_rule_i`, `meta_mark`, `first_order` and `learn_types`, the
float gate, and the moved examples. Probes are in the review scratch folder
(`p1.sw` to `p6.sw`), run with the lane's release binary; "main" below is the
main checkout's release binary of 15:05, which has rules K and S.

## Verdict

**Sound as far as I could attack it; one decision for Matt before it
merges (F1), which is a narrowing under the brief's question 8.** Nothing
false got through. Rule I's design holds: the kernel's marks are the
kernel's, every kernel caller of `conv` hands over two values of one type,
and the one place that didn't (two definitions' scrutinees) no longer
compares them. But rule F, with rule S stopping short of indexed
propositions that have fields, leaves one family of programs that checked
before and are refused now, and makes conversion non-transitive on the same
family. Both go away with one extension of rule S, which is scope.

## Findings

### F1 (medium; decision for Matt): a match into data on an indexed proposition whose constructor has proof fields

`E-PROP-ELIM` allows it, rule S doesn't cover it (D3724 took Lean's rule:
indexed needs no fields), and the proposal says this case "goes back to Matt
before stage 4" if the counter finds any; it found none in our code, so it
never went. Rule F now makes it matter:

```
type Q2: Nat → Prop = | MkQ2 (w: 0 = 0): Q2 0
def f (x: Nat): Q2 x → Nat
  | MkQ2 w => 5
def pf: Q2 0 := MkQ2 byComputing
def mkQ (b: Bool): Q2 0 := match b with | True => MkQ2 byComputing | False => MkQ2 byComputing
```

- **Narrowing.** `theorem n1: f 0 pf = 5 := byComputing` and `theorem n8:
  f 0 (mkQ True) = 5 := byComputing` check on main and are refused on the
  lane (E-REFL): the scrutinee is a call of a proof *definition*, which
  unfolded to the constructor before and is frozen now, and rule S leaves
  the `case` stuck. (A theorem as the scrutinee was already stuck since
  sealing.) This is the only loss of computation I could find from rule F:
  a cast reads its ends (rule K), a non-indexed one-shape match and an
  indexed one without fields are rule S's, and `Decidable`-style data
  holding proofs computes as before (`isYes decZero = True` checks).
- **Not transitive.** With `s: Q2 0` a variable, the lane accepts
  `f 0 s = f 0 (MkQ2 byComputing)` (by arguments: rule I on `s` against
  the constructor) and `f 0 (MkQ2 byComputing) = 5` (the literal
  constructor takes its branch), and refuses `f 0 s = 5`. Main refuses the
  first, so this is new. It isn't unsound (all three are true, and
  `Eq.trans` of the two accepted ones proves the third), but `docs/core.md`
  says "the relation stays an equivalence" and that comparing by arguments
  "agrees [with unfolding] because unfolding never reads a proof", and the
  notes' transitivity section says the same. Here unfolding does read one:
  the literal constructor. It is Lean's `Acc` non-transitivity, which the
  proposal's 4.4 set out to avoid.

Ways out, all Matt's (D3688-style scope): (a) rule S also fires for an
indexed one-constructor proposition with proof fields when the indices
agree, the fields bound to stand-ins (accepts more, restores both
properties; the stand-in `Proj` today requires no indices); (b) accept it as
Lean does, and say so in `docs/core.md` and the notes; (c) refuse such
matches in `E-PROP-ELIM` or keep the literal stuck too (accepts less). I'd
take (a) as a follow-up ticket and merge this lane on (b)'s wording
meanwhile, if Matt agrees the narrowing can stand for that long: no code in
the repo is affected (stage 3's counter), but scope is the grammar.

Repro: `p3.sw` (n1, n8) and `p6.sw` (t1, t3, t4) in the review scratch.

### F2 (low, docs): `docs/core.md` overstates

"The relation stays an equivalence" and "unfolding never reads a proof"
need F1's exception until it is closed. The run-time paragraph already says
such a match "stays stuck"; it should add "unless the proof is a literal
constructor".

### F3 (low, unverified): an elaborator variable's mark can outlive a solution taken back

`Ctx::mark_of_type` forces the binder's type through the solutions of the
moment and stores the mark on the variable for good. A type whose sort is
itself an unknown (`x: ?A`, `?A: ?s`) could give *proof* under a trial
solution that is then undone. `meta_mark` guards against this by epoch
(condition G); a bound variable's mark has no such guard. Elaborator only:
the kernel derives its own marks and re-checks, so the cost would be a
wrong elaborator answer the kernel refuses, not a false theorem. I did not
build a repro. Ticket, not a blocker.

### F4 (note): `marks_agree` lets *unknown* match either mark

`identical` treats an unknown mark as agreeing with *proof* or *not proof*,
so a tree-memo "equal" found by rule I on a pair with proof-marked variables
would be reused for a pair alike but for unknown marks. In the kernel
nothing compared carries an unknown mark on a variable (the remaining
`Value::var` sites are `determined.rs`, a type walk in `check.rs` and
`unify_index.rs`'s solutions, none compared with marked twins in one
comparison), and the unifier's answers are re-checked, so I count it sound;
but "unknown agrees" is only safe in the direction unknown-first. Strict
equality of marks in `identical` would cost a few memo hits and remove the
argument. Ticket.

## What I checked and found sound

1. **Rule I fires only on kernel marks.** `value::is_proof` reads a
   variable's binder mark, `Def::proof`, a data type's sort, a `J`'s result
   mark and a field's sort; the kernel derives each (`prop_mark` now derives
   a function type's binder mark too, F2 of SW-4671), refuses a given mark
   that differs, and the cache re-check clears marks first
   (`cleared_marks_are_derived_again` passes). No cumulativity and no
   universe polymorphism, so a type has one sort and a family can't return
   `Prop` at some arguments and `Type` at others (probe: `W: Bool → Type 1`
   with a `Prop` branch is E-UNIVERSE). Probes refused as they must be:
   two propositions, two predicates, data of a `Type` family, functions
   from a proof to data, lambdas over a proof binder with different data
   bodies, data variables bound after a proof, a record differing in a data
   field beside a proof field, `Quot.mk 0 = Quot.mk 1`, two values of a
   quotient, values of `Fam p` and `Fam q`, and proofs of different
   propositions (E-TYPE-MISMATCH before `conv` is asked). Accepted, and
   true: proofs of a `Prop` family, of a computed proposition, functions
   into a proposition, `MkWrap 0 = MkWrap 1` in a `Prop`.
2. **Homogeneity at each kernel call of `conv`.** Type against type
   (`check.rs` 659, 707; types are never marked proofs); constructor indices
   left to right, stopping at the first difference; `Refl`'s two sides;
   index unification compares the binder types first (`unify_index.rs`
   181); rule K's ends and rule S's indices. Inside `conv`: spines of one
   head left to right; two stuck casts by ends' type, ends, motive, base,
   never their proofs; data parameters and constructor fields in order.
   The exception was two different definitions' `case` scrutinees, which
   needn't have one type: for a proposition they are now not compared at
   all. I tried to break that (`p2.sw`: `f x s` against `g y t` and `h y t`
   over `Q x`, `Q y`, and a proposition with a parameter-dependent proof
   field): nothing false is accepted, and the argument holds: leaves are
   evaluated each in its own arguments, a data leaf can't depend on the
   shared field variables except through positions rule I already equates,
   and `E-PROP-ELIM` refuses a data field the indices would determine
   (D140), which is the case that would have made it unsound.
3. **Memo keys.** `CallMemo` keys by unfolding cells, so the values, marks
   included, are the same. The tree memo's `identical` compares marks (see
   F4). No mode is left to key by.
4. **Rule F.** `frozen` is read through `body_seen`, `unfold_now` and the
   reference evaluator's `unfold` and `seen`, written apart. Abel-Coquand
   checks in 0.4 s. The soundness set passes (1 test), so every example
   still refused fails with its stated code; `index-proof-conflict` is now
   E-NOT-EMPTY, rightly (the equation between two proofs is deleted).
5. **Examples moved to accept**: each is two proofs compared (04, 12, 19,
   23, 25 both, `quot-ind-computes`), a type differing in a proof (13), or
   data calls differing in a proof argument with rule K doing the cast (22,
   24, `char-arm-opaque-call`). All true in the model.
6. **Floats.** `Float.make` keeps its witness; the gate rewrites
   constructors' proof fields to `byComputing` before comparing normal
   forms, so data fields (the bits) are still compared exactly.
   `float::the_float_natives_agree_with_their_definitions` passes. The pins
   that moved are the natives that build a `Float` (they reach
   `Float.make`); the predicates' didn't.
7. **Unifier.** Condition D is in `first_order` (rule I only after
   `learn_types` unified the types, else only the same value); `meta_mark`
   is kept by epoch and trail length. `mark_of_type` returns a decided mark
   only from an equation, a data type's sort or a head's type applied down
   to a sort, and its fresh variables sit a million above the context, so
   they are never looked up as context variables.

Tests run: `examples::soundness` (1 passed); `proofs`:
`proof_equivalence` and `proof_masks` (24 passed); the float gate test (1
passed).

## What I didn't check

- `unify.rs` beyond the functions named (the diff is about 600 lines), and
  `matching.rs`'s `same_shifted_but_proofs` (condition E): elaborator code
  the kernel re-checks, so completeness and error quality, not soundness.
- Anything under the `reference` feature at run time: the tripwire
  (`by_rule_i`'s panic), the point-of-use assert on `Refl` and the cast-ends
  assert were read, not fired. Whether ordinary code can trip the panic in a
  reference build is the suites' to show.
- The hash snapshots (about 200 moved), the whole examples suite, std,
  AoC, `tools/fmt` and the roguelike: the verifier's and Overmind's. Given
  the memory note on elaborator-route changes, a whole `tools/fmt check
  --no-cache` belongs in the verifier's run.
- `docs/core.md` line by line: I read "Proof irrelevance", "Proof marks"
  and the run-time paragraph against the code (F2 is the one mismatch).
- The roughly 15 unmarked elaborator variables the notes list.

## Tickets to file

1. Rule S for an indexed one-constructor proposition with proof fields
   (F1(a)), or the decision recorded if Matt picks (b) or (c).
2. `docs/core.md` and the notes: the exception to "equivalence" (F2), with
   this lane if it merges on (b).
3. Elaborator variable marks and undone solutions (F3): find a repro or
   show there is none.
4. `identical`: strict mark equality (F4).
5. The unmarked elaborator variables sweep (already in the notes).
