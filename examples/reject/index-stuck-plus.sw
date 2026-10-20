-- expect-error: E-INDEX-STUCK
-- Matching a `Vec a (n + m)` with `n` unknown: `VNil` would need
-- `n + m = 0`, which doesn't compute, so whether `VNil` can be here can't
-- be decided. Pairs with `lengthOfSum` (which matches `n` first) and
-- `append` in accept/indexed-families.sw
-- (docs/proposals/indexed-families.md §9, test 4).
type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def lengthOfSum: Vec a (n + m) -> Nat
  | VNil      => 0
  | VCons _ _ => 1
