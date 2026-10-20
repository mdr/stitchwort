-- expect-error: E-INDEX-STUCK
-- A constructor declared with length `n + 1`: `+` counts down its first
-- argument, so `n + 1` doesn't compute while `n` is unknown, and `VCons`
-- can never be matched on a `Vec a (Succ k)`. Pairs with `head` in
-- accept/indexed-families.sw, where `VCons` is declared with `Succ n`
-- (docs/proposals/indexed-families.md §9, test 5; D145).
type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (n + 1)

def head: Vec a (Succ n) -> a
  | VCons x _ => x
