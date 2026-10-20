-- expect-error: E-EXPORT
-- An indexed family can't cross the JS boundary: decoding would have to
-- check its index (paired with extract/vec-inside.sw).
type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

export def head: Vec Nat (Succ n) -> Nat
  | VCons x _ => x
