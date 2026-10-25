-- expect-error: E-EXPORT
-- ...also inside a container.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

export def count: List (Vec Nat 3) → Nat
  | Nil       => 0
  | Cons _ vs => Succ (count vs)
