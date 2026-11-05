-- expect-error: E-REFL
-- The glued shortcut compares constructors' proof fields: `Box.unbox (MkBox
-- p)` and `Box.unbox (MkBox q)` compute to `p` and `q`, glued or not.
-- Partner: `boxEq` and `unboxComputes` in accept/proof-irrelevance.sw.

type Box (a: Prop): Type =
  | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

theorem unboxBoth (a: Prop) (p: a) (q: a): Box.unbox (MkBox p) = Box.unbox (MkBox q) := rfl
