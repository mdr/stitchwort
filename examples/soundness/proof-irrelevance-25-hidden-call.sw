-- expect-error: E-REFL
-- A hidden opaque call's arguments are compared in the shortcut mode, which
-- compares proof fields: where `ou` is transparent, the two compute to `p`
-- and `q`. Partner: `ouSame` in accept/proof-irrelevance.sw; with `ou`
-- unfolded: proof-irrelevance-25-unfolded.sw.

type Box (a: Prop): Type =
  | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

opaque def ou [a: Prop] (b: Box a): a := Box.unbox b

theorem t25 (a: Prop) (p: a) (q: a): ou (MkBox p) = ou (MkBox q) := rfl
