-- accept/proof-irrelevance-25-hidden-call.sw, with `ou` unfolded: the two
-- compute to `p` and `q`, equal by rule I (docs/core.md, "Proof
-- irrelevance").
-- Was soundness/proof-irrelevance-25-unfolded.sw, refused (E-REFL) before rule
-- I (stage 5 of docs/proposals/full-proof-irrelevance.md).

type Box (a: Prop): Type = | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

opaque def ou [a: Prop] (b: Box a): a := Box.unbox b

theorem t25 ∀ (a: Prop) (p q: a): ou (MkBox p) = ou (MkBox q) unfolding ou := byComputing
