-- expect-error: E-TYPE-MISMATCH
-- The subject-reduction gap (docs/proposals/proof-irrelevance.md §5.7):
-- `castViaBox a p q f x rfl` computes to `x`, but `x` itself isn't accepted
-- at `f q`. Partner: `castOk` in accept/proof-irrelevance.sw.

def bad (a: Prop) (p: a) (q: a) (f: a → Type) (x: f p): f q := x
