# SW-4686: Fable review of rule S for indexed propositions with proof fields (D3727)

Reviewed: `aa9f60471` on `lane/SW-4686`, against its merge base with `main`.
Compared with a binary built from `main` after stage 5 ("old" below).
23 Nov 2026.

## Verdict

**Sound; merge.** I found no way to get a false equation through, and the
lane's argument (docs/reviews/SW-4686-notes.md) holds. Every probe that
should stay stuck does, in the kernel with and without
`STITCHWORT_DEBUG_FORCE_UNGLUED`, and nothing that checked on the old
binary is refused.

One correction to what the change claims, not to what it does: it closes
the corner the stage 5 review's F1 named (the triple `t1`/`t3`/`t4`), but
conversion is **still not transitive**, and the new text in `docs/core.md`
says it is. The remaining corner is a match on a *field of an enclosing
match* (F1 below). It is older than this lane (it is there for D3724's
no-field case on the old binary too) and nothing false is accepted through
it, so it doesn't block the merge; the doc sentence should be fixed and the
corner ticketed.

## Findings

### F1 (medium; not introduced here): a match on a field of an enclosing match keeps conversion non-transitive, and unstable under substitution

Rule S's indexed case reads the scrutinee's type off the definition's own
type, so it fires only for a `case` on a parameter. A `case` on a proof
field bound by an enclosing match stays stuck on any proof but a literal
constructor, which is F1 of the stage 5 review one level down:

```
import Std (Eq, Nat)

type Q2: Nat → Prop = | MkQ2 (w: 0 = 0): Q2 0
type Outer: Prop = | MkOuter (q: Q2 0)

def g: Outer → Nat
  | MkOuter q => match q with
    | MkQ2 w => 5

theorem a1 ∀ (o: Outer): g o = g (MkOuter (MkQ2 byComputing)) := byComputing  -- checks (rule I on the arguments)
theorem a2: g (MkOuter (MkQ2 byComputing)) = 5 := byComputing                 -- checks (literal constructors)
theorem a3 ∀ (o: Outer): g o = 5 := byComputing                               -- E-REFL
theorem a4 ∀ (s: Q2 0): g (MkOuter s) = 5 := byComputing                      -- E-REFL
```

Same answers on the old binary and the lane's. The same triple with a
no-field indexed proposition inside (`MkOuter (q: Same Nat 0 0)`, inner
`| MkSame => 5`) behaves the same way on both, so this corner has been
there since D3724 plus rule I; the stage 5 review (mine) missed it.

It also makes the answer depend on substitution. With a variable result so
both sides stay open:

```
def gk (k: Nat): Outer → Nat
  | MkOuter q => match q with
    | MkQ2 w => k

def po: Outer := MkOuter (MkQ2 byComputing)

theorem b1 ∀ (k: Nat): gk k po = gk k (MkOuter (MkQ2 byComputing)) := byComputing   -- checks
theorem b1c: gk 5 po = gk 5 (MkOuter (MkQ2 byComputing)) := byComputing             -- E-REFL: "`gk 5 po` and `5` aren't equal"
```

`b1c` is `b1` at `k := 5`. I did not find out which layer refuses `b1c`
(the kernel's `conv`, or a closed-goal path of `byComputing` that evaluates
both sides before comparing them).

Nothing false is accepted: all of these equations are true, and `Eq.trans`
proves `a3` from `a1` and `a2`. It is a completeness and predictability
gap, of the kind D3727 decided to close.

Rewriting the inner match as a call to a helper whose scrutinee is a
parameter (`| MkOuter q => h 0 q`) fires with this lane (it didn't
before), as does an inner `match f 0 with …` on a non-variable scrutinee,
which the elaborator lifts to a function of its own. So the gap is exactly
a `case` on a constructor field inside one case tree.

**Fix direction** (a follow-up lane, Opus): let the indexed test find the
type of a scrutinee that is a field. When the enclosing `case` bound the
field (by iota or by rule S), its type is the field's declared type over
the enclosing scrutinee's parameters and earlier fields, the same
computation `infer_proj` does; or record the scrutinee's type on the `case`
node. The index test and its soundness argument are unchanged, since they
only need *a* correct type for the scrutinee.

### F2 (low, docs): `docs/core.md` now says conversion is transitive

Three places in the lane's `docs/core.md` text overclaim, given F1:

- Rule S: "With fields covered, a literal constructor and any other proof
  of its type compute alike, which keeps conversion transitive under rules
  I and F".
- Proof irrelevance: "the relation stays an equivalence … A match into data
  on a one-constructor proposition is where a literal constructor and an
  unknown proof could part, and rule S takes the branch on both", and
  later "where a literal constructor computes, rule S computes the same on
  any proof of its type".
- Running a program: the list of what stays stuck does name "a field of an
  enclosing match", but the old sentence's "(the one corner where
  conversion isn't transitive)" went with the exception.

The stage 5 exception is otherwise fully removed (no leftover "no indices
and only proof fields" or "constructor has fields stays stuck" in
`docs/core.md`, `docs/syntax.md`, `docs/guide/` or the kernel's comments).
Suggested wording: say rule S covers a `case` on a definition's parameter,
and that a `case` on a field of an enclosing match is the one corner left
where a literal constructor and another proof part, with the `g`/`Outer`
example above, until the follow-up lands. The header comment of
`examples/accept/proof-irrelevance-39-indexed-field-transitive.sw`
("Conversion stays transitive …") wants the same qualifier.

### F3 (low, tests): the reference evaluator's new path is tested on one shape

`reference.rs` `rule_s` is separate code and I read it against `one_shape`:
same environment (parameters, then one projection per field, in field
order), same index-by-index comparison stopping at the first difference.
But the four-way test (`proof_masks.rs` `t39`/`t39p`) exercises only `Q39`,
whose index mentions no field. An index that mentions a field
(`ByProof`), where the comparison is `Proj(…)` against a proof by rule I
*inside the reference's `conv`*, and fields that mention parameters
(`AtThree`), are checked only through the kernel, by the accept example. I
found no CLI route to run my probes through the reference. Worth two more
`CASES` rows.

## What I checked and found sound

**The argument.** Steps 1 to 4 of the lane's notes hold. The one that
carries the weight is step 2: the rule fires only when the constructor's
result indices, over the scrutinee's parameters and its own projections,
are `≡` the scrutinee's indices, so `C ps (Proj …)` has the scrutinee's
type and the branch's refinement is an equation that already holds. In a
consistent context `n: D ps is` is, in the model, `C` applied to some
fields, and the branch run with `Proj(D, k, n)` differs from the branch run
with those fields only in proofs. In an inconsistent context anything
follows anyway. So any unsoundness would have to be an implementation
slip in the index test, which is where I looked.

**`infer_proj` dropping the indices (question 2).** Right for every type
that passes the shape test. A constructor's field types are terms over the
parameters and earlier fields; `Value::Data`'s arguments are parameters
then indices (the layout `one_shape` relies on too), so `truncate` leaves
exactly the environment the field types were written in. For a type with
eta the truncation does nothing (no indices). The projection is derivable
without the rule (a `case` into `Prop` with a motive constant in the
indices), so no new inhabitants. A data field fails the shape test
(`field_sorts`), and `E-PROP-ELIM` refuses the match separately, including
a data field forced by an index (`MkIsZ (n: Nat) (h: n = 0): IsZ n`).

**Probes (question 1).** All on the lane's binary; "stuck" means
`byComputing` refused with `E-REFL`. Each "fires" case was stuck on the old
binary.

| Shape | Fires | Stays stuck |
|---|---|---|
| a parameter and two indices, one computed: `MkT (h: a = a): T a (a + 1) 0` | `T a (a + 1) 0` | second index `1`; first index `a`; `b + 1` for another variable; an unknown `x` |
| the branch's result typed by the index: `conv (x): Q x → V x` returning `VZ` | `Q 0` | `Q 1` (would give `VZ: V 1`); `x` with a hypothesis `x = 0` (not definitional) |
| heterogeneous-equality-like: `HRefl (w: 0 = 0): HEq a x a x`, the branch returning `v: a` at `b` | `HEq Nat x Nat x` | `HEq Nat 0 Bool True`; an unknown type `b`; `HEq Nat x Nat y` |
| an index that is a type: `MkTI (w: 0 = 0): TI Nat` | `TI Nat` | `TI Bool` |
| an index computed from a field by a function on proofs: `MkFI (w: 0 = 0): FI (pn w)`, `pn` matching `byComputing => 3` | `FI 3` (rule K inside the index, on the projection) | `FI 4` |
| an empty family: `MkEm (w: 0 = 1): Em 0` | `Em 0` (harmless: the context is inconsistent, and a cast along the projected `0 = 1` stays stuck by rule K) | |
| dependent fields, an index that is a field: `MkDep (h: P2 a) (k: h = h): Dep a h a` | `Dep a p a` (the index `Proj` against `p` by rule I, after the data index agreed) | `Dep a p 0` |
| a parameter the index repeats: `MkPI (h: a = 0): PI a a`, the branch returning `v: V x` at `V a` | `PI a a` | `PI 0 1` (would give `VS 0: V 0`) |
| two indexed scrutinees in one definition | both agreeing | one apart |
| the scrutinee before a later parameter; an inner `match f 0 with` | both | |
| recursion: `MkA (k: Nat → A 0): A 0`; through a wrapper, `MkC (k: Wrap (C 0)): C 0` | | `E-PROP-ELIM` (so rule S can't unfold without end) |

The order of the index comparison matters where a later index's type
depends on an earlier one (rule I needs both proofs at one type): both
evaluators stop at the first difference, in order.

`Quot`: reasoned, not run. An index of quotient type is compared by `≡`
like any other, so `QI (Quot.mk 1)` against a constructor at `Quot.mk 0`
stays stuck whatever `Quot.sound` proves; the cast along `Quot.sound` is
rule K's and untouched.

**Transitivity of F1's triple (question 3).** `t1`, `t3`, `t4` and `n1`
all check (`examples/accept/proof-irrelevance-39-indexed-field-transitive.sw`),
with and without `STITCHWORT_DEBUG_FORCE_UNGLUED`. See F1 above for what
remains.

**The reference evaluator (question 4).** Agrees by reading, and on `t39`
and `t39p` by test. See F3.

**Scope (question 6).** The change only removes a "return false" and
widens a shape test, so the rule fires in more cases and `Proj` is typed in
more cases; no path refuses more. Every probe that checked on the old
binary checks on the new.

**Tests run.** `examples::soundness_examples_fail_for_the_expected_reason`
(pass) and `proof_masks::every_case_gets_its_answer_four_ways` (pass), one
at a time; 13 probe files against both binaries.

## What I didn't check

- Which layer refuses `b1c` in F1.
- The reference evaluator on anything but `Q39` (F3).
- A `Quot` probe (reasoned only).
- The elaborator's unifier: whether it needs the same extension to solve
  through such a match (completeness only; the kernel rechecks).
- Universe-polymorphic families, and a proof field whose type is a
  parameter of sort `Prop` beyond `Both`-style examples.
- Performance: the index test now builds one projection per field per
  attempt; stage 3's counter found no such match in the repo, so I didn't
  measure.

## Tickets to file

1. Rule S on a field of an enclosing match (F1): find the field's type so
   the indexed test can fire there; add the `g`/`Outer` triple and the
   `b1`/`b1c` pair as examples; find which layer refuses `b1c`. Opus,
   Fable-reviewed.
2. `docs/core.md` and example 39's header: qualify the transitivity claims
   (F2). Small enough to fix on this branch before merging.
3. Two more `proof_masks` cases for the reference evaluator: an index that
   mentions a field, fields that mention parameters (F3). Sonnet or
   DeepSeek.
