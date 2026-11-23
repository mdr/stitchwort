-- Two proof variables are equal anywhere, not only at a proof position:
-- rule I (docs/core.md, "Proof irrelevance").
-- Was soundness/proof-irrelevance-12-bare-proofs.sw, refused (E-REFL) before
-- rule I (stage 5 of docs/proposals/full-proof-irrelevance.md).

theorem pi ∀ (a: Prop) (p q: a): p = q := byComputing
