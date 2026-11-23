-- `f p` and `f q` are the same type, as `p` and `q` are equal by rule I
-- (docs/core.md, "Proof irrelevance"): this closes the subject-reduction gap
-- of docs/proposals/proof-irrelevance.md §5.7, where `castViaBox a p q f x
-- byComputing` computed to `x` but `x` wasn't accepted at `f q`.
-- Was soundness/proof-irrelevance-13-subject-reduction-gap.sw, refused
-- (E-TYPE-MISMATCH) before rule I (stage 5 of
-- docs/proposals/full-proof-irrelevance.md).

def bad (a: Prop) (p q: a) (f: a → Type) (x: f p): f q := x
