-- expect-error: E-NONEXHAUSTIVE
-- The same match at an unknown length: `VNil` is possible, so the one arm is
-- not enough (and finding that runs without the library's `Fin`).
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def head (items: Vec Nat n): Nat :=
  match items with
    | VCons x _ => x
