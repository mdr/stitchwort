-- expect-error: E-REFL
-- proof-irrelevance-25-hidden-call.sw, with `ou` unfolded: the two compute
-- to `p` and `q`.

type Box (a: Prop): Type =
  | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

opaque def ou [a: Prop] (b: Box a): a := Box.unbox b

theorem t25 (a: Prop) (p: a) (q: a): ou (MkBox p) = ou (MkBox q)
    unfolding ou
:= rfl
