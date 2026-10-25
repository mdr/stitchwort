-- expect-error: E-NONEXHAUSTIVE
-- A missing constructor in a `match` expression on an indexed family is
-- worded as on any other type: no alternative of this `match` matches it.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def head (items: Vec Nat 1): Nat :=
  match items with
    | VNil => 0
