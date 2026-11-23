# SW-4686: rule S for indexed propositions with proof fields (D3727)

For a Fable review. Closes the one non-transitive corner left by full proof
irrelevance stage 5 (docs/reviews/SW-4674-fable-review.md, F1).

## The change

| Where | What |
|---|---|
| `value.rs` `one_shape` | the indexed case no longer requires a constructor without fields; the constructor's result indices are evaluated over the scrutinee's parameters **and its fields read as `Proj(D, k, n)`** of the scrutinee `n`, then compared with the scrutinee's indices as before (`meet_in_evaluation`) |
| `reference.rs` `rule_s` | the same, independently: fields as `project(env[level])`, compared by the reference `conv` |
| `check.rs` `infer_proj` | `Proj(D, i, t)` accepted for a one-constructor proposition with only proof fields **with or without indices**; for an indexed `D`, `t ⇒ D ps is` and the field's type is evaluated over `ps` only (the indices are dropped) |

Unchanged: one constructor; every field a proof; the definition's result is
data; the scrutinee is one of the definition's own parameters (its type read
off the definition's type, so a `case` on a field of an enclosing match stays
stuck); the indices must be `≡`; `E-PROP-ELIM` still refuses a match into
data on a proposition that is recursive, nested, in a group, or has a data
field (rule S relies on that, as the unindexed case already did).

## Soundness argument

Write `n : D ps is` for the scrutinee, `C` for `D`'s one constructor with
proof fields `h_0 … h_{m-1}` (types `A_k` over the parameters and earlier
fields) and result indices `r(ps, h)`.

1. **The projections are well typed.** `Proj(D, k, n) : A_k[ps, Proj(D, j<k, n)]`.
   This is derivable without the new rule: a `case` on `n` into `Prop` (always
   allowed) with motive `λ is' _. A_k[ps, Proj(D, j<k, ·)]`, which doesn't
   mention the indices because a field's type is written over the parameters
   and earlier fields only; the earlier projections inside the motive are
   handled by induction on `k`, and in the branch `Proj(D, j, C h) ⟶ h_j`. So
   `infer_proj`'s extension adds no new inhabitants: it is a proof out of a
   proof, as the unindexed case (SW-4673) is. It holds even where the
   indices don't match any constructor (then `D ps is` is empty and anything
   follows anyway).
2. **The constructor applied to the projections has the scrutinee's type.**
   `C ps (Proj(D, k, n))_k : D ps r(ps, Proj(D, ·, n))`, and the rule fires
   only when `r(ps, Proj(D, ·, n)) ≡ is`. So `C (Proj …) : D ps is`.
3. **So `n ≡ C (Proj …)` by rule I**: two proofs of the same proposition.
4. **And `case n` into data takes the branch for `C` with `h_k := Proj(D, k, n)`**,
   which is iota on `C (Proj …)`, the term `n` is convertible with. The
   branch was checked under the refinement `is := r(ps, h)`; with `h` bound
   to the projections that refinement is step 2's equation, which holds, so
   the step preserves types (subject reduction, as for the no-field case).

In the model (proofs as the unit of each inhabited proposition,
docs/proposals/full-proof-irrelevance.md §3), `n` and `C (Proj …)` denote the
same element, so the step is an equation the model already makes.

**Termination.** The step removes a `case` and adds none; the projections
are stuck neutrals. A recursive `D` could loop (`f (MkR r) = f r` would
become `f (Proj …)` again and again), but `E-PROP-ELIM` refuses a recursive
proposition into data, and with a field present the "every branch
impossible" exemption doesn't apply when the rule fires (step 2's indices
agree, so the branch isn't impossible). Same reliance as the no-index case,
which the SW-4673 Fable review accepted.

**Indices that mention fields.** A result index may mention a proof field
(`MkByProof (h: 0 = 0): ByProof h`). It is evaluated with the projection
bound, so the comparison is `Proj(ByProof, 0, s) ≡ h`: two proofs, equal by
rule I, as in step 3. A data index computed from a proof field (`T (g h)`)
reads the proof only through `g`, which rule F never lets look inside a
proof: `g (Proj …)` computes only if `g` ignores its argument, and then it
computes alike for every proof.

**What stays stuck, and why it must:**
- indices that differ (`f 1 s` for `s: Q2 1`): step 2 fails, `C (Proj …)`
  isn't of type `D ps is`, and the branch's refinement would be false;
- indices not yet known equal (`f x s`): the comparison can't show them
  `≡`, so stuck (completeness, not soundness);
- a `case` on a field of an enclosing match: its type isn't read off the
  definition's type, so the rule doesn't fire (as before);
- data fields and recursive propositions: `E-PROP-ELIM`.

The converse direction (that nothing became stuck which computed before) is
immediate: the rule only fires in more cases, and the no-field and unindexed
cases are unchanged (an empty field list gives the same environment).

## Examples

- `examples/accept/proof-irrelevance-39-indexed-field-transitive.sw` (moved
  from `soundness/…-39-indexed-field-not-transitive.sw`): `t4` and `n1` now
  check.
- `examples/accept/rules-k-and-s.sw`: `withFieldAny` (was
  `soundness/proof-irrelevance-34-indexed-with-field.sw`, removed),
  `threeAny` (fields mentioning parameters), `byProofAny` (an index that
  mentions a field).
- `examples/soundness/proof-irrelevance-40-indexed-field-indices-differ.sw`
  (`E-REFL`): apart indices. (An unknown index and a `case` on an enclosing
  match's field also stay stuck, but those are completeness limits, not
  soundness ones: the probes are in the lane's report, not in `soundness/`.)
- `examples/soundness/proof-irrelevance-41-indexed-field-data.sw`
  (`E-PROP-ELIM`): a data field, a recursive field.
- `crates/driver/tests/proofs/proof_masks.rs` test 39 (and its apart
  partner), answered the same four ways (glued, no shortcuts, unglued,
  reference).

## Questions for the review

- Is dropping the indices in `infer_proj` right for every indexed `D` that
  passes the shape test, including one whose constructor's field types
  mention a parameter that the indices also constrain? (Argued in step 1:
  the field types never mention the indices.)
- `one_shape` binds the fields to projections of the forced neutral, not of
  the scrutinee as it was (rule 2's `eta_fields` keeps a glued call); for
  proofs this only affects what a goal shows, never what is equal.
