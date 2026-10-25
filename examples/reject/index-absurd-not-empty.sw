-- expect-error: E-NOT-EMPTY
-- `()` needs a type with no possible constructor here. A `Vec a n` can be
-- `VNil` (when `n` is 0) or `VCons`, so it has values. Pairs with
-- `notEvenOne` in accept/indexed-families.sw, where `Even 1` has none
-- (docs/proposals/indexed-families.md §9, test 3).
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def nothing: Vec a n → Nat
  | ()
