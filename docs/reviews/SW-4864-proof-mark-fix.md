**SOUND WITH CHANGES**: fall back to the old forcing path when the new early path answers *unknown* (C1), and update two doc sentences (C2). No unsoundness found.

# SW-4864 (a type call's proof mark read from its definition): Fable review

Reviewed `33b81254e` in `.claude/worktrees/scratch-sw-4864`, 26 Nov 2026, by reading only (nothing built or run): the diff, `mark_of_type`, `is_proof`, `force`/`needs_forcing`, `Value::Call`'s contract, the kernel's `sort_of_stuck`/`type_of_stuck`, the callers in `crates/elab`, `docs/core.md` "Universes" and "Proof marks".

## 1. Soundness: holds

- **What actually changes.** `force` leaves `Neutral(Head::Def, _)` alone (`needs_forcing` is true only for a solved unknown's head and for `Value::Call`), so for that arm the new early return is exactly the old arm. Only `Value::Call` (a glued call, all parameters applied) behaves differently: its sort is read off `Def::ty_value` instead of off its unfolding.
- **The two readings can't disagree as Proof against NotProof.** core.md: no cumulativity, every type has one sort, a body is checked `≡` its declared type. So a call `D args : Sort s` by the declared type unfolds to a type of the same sort `s`, and the old path's answers (an equation, a data type's sort, a function type's codomain's) are that same `s`. A definition declared at one sort with a body at another isn't accepted by the kernel.
- **The new path over-claims nowhere.** It answers only when the declared type, walked by the spine's applications through forced `Pi`s, ends in a forced `Sort`. A projection in the spine (a field of a call, `project_call`), a non-`Pi` step or a non-sort end is *unknown*. A partial application is never a `Call`, and applying a `Call` forces it first (`apply_call`), so there's no over-applied spine either. Opaque definitions, axioms and assumptions are `Neutral`, unchanged. A declared type that is itself a call (`def lt: Rel Nat`) is forced inside `mark_of_head`, as before.
- **This is the kernel's own method.** `check.rs` `sort_of_stuck` already reads a call's sort off `ty_value` without forcing; the lane makes the elaborator's reading agree with it.
- **Marks disagreeing between forced and unforced forms can't matter.** `mark_of_type` has only elaborator callers (`Cx::mark_of_type`, binding variables; two `kcx.bind` in trial checks whose terms the kernel checks again). `Head`'s equality and hash ignore the mark; rule I asks only "both Proof?"; the kernel derives every mark itself and trusts none. The only disagreement possible is decided against *unknown*, the safe side.
- The new path decides some cases the old left *unknown* (an unfolding headed by an unknown or a projection). Those answers are right for the same reason; more complete.

## 2. Completeness: two cases lose a mark (Proof or NotProof becomes Unknown)

Unknown only stops rule I firing in the elaborator's comparisons; the lost case that matters is old = Proof.

- **R1, a field of a call used as a type.** `Call(id, [args.., Proj])`: the old path forced it to the field's value and marked it; the new path stops at the projection. Example (not run): `type Spec = { holds: Prop }`, `def spec (n: Nat): Spec := { holds := n = n }`, a binder `h: (spec n).holds`: was Proof, now Unknown. (Dictionaries don't glue, so instance fields aren't affected.)
- **R2, a declared type the walk can't read.** The result sort or a `Pi` hidden behind something `force` leaves stuck (an opaque alias hidden at this point, a stuck call in the signature): the old path unfolded the call's body and often decided; the new path says Unknown.

Both are narrowings in principle (two proof variables of such a type no longer unify by rule I), so under D3688 they'd be Matt's; C1 removes both, so there's nothing to ask him.

**C1 (required).** In the early arm, return only a decided mark, and otherwise fall through to the old code:

```rust
if let Value::Neutral(Head::Def(id), spine) | Value::Call(id, spine, _) = &ty
    && let Ok(mark @ (ProofMark::Proof | ProofMark::NotProof)) =
        mark_of_head(g, g.def(*id).ty_value.clone(), spine)
{
    return Ok(mark);
}
```

Then the new function's answer is the old one wherever the old one was decided (by §1 they agree), and `cost < 5` still returns without forcing. The forcing cost returns only for R1/R2 shapes; extending `mark_of_head` to projections as `type_of_stuck` does would remove R1's, a follow-up, not needed here.

## 3. Docs

**C2.** `docs/core.md` "Proof marks" says the elaborator marks from "an equation, a data type's sort, a function type's codomain, a stuck type's head". Add that a call is read from its definition's type without unfolding it (with C1: unfolded only when that doesn't decide). `mark_of_type`'s own doc comment ("or a stuck type's head type") wants the same clause. Nothing else in core.md is affected: the kernel's rules don't change.

## Other

- The commit adds no test; it names bench `check_work` as the one that caught it, which meets D3608 if that test failed before (I didn't run it). A small `proof_marks.rs` case for R1 (a field of a call that is a proposition marks Proof) would pin C1.
