-- `Box.unbox (MkBox p)` and `Box.unbox (MkBox q)` are proofs, so equal by
-- rule I (docs/core.md, "Proof irrelevance"), unfolded or not.
-- Was soundness/proof-irrelevance-19-unbox-both.sw, refused (E-REFL) before
-- rule I (stage 5 of docs/proposals/full-proof-irrelevance.md).

type Box (a: Prop): Type = | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

theorem unboxBoth ∀ (a: Prop) (p q: a): Box.unbox (MkBox p) = Box.unbox (MkBox q) := byComputing
