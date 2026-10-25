-- expect-error: E-LET-REFUTABLE
-- A constructor pattern on an indexed family that leaves a possible case
-- out is refutable in a `let`, as on any other type.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def first (items: Vec Nat 1): Nat :=
  let VNil := items
  0
