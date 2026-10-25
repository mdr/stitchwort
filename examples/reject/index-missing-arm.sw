-- expect-error: E-NONEXHAUSTIVE
-- Only an impossible constructor may be left out. Here both vectors can be
-- `VCons`, and no arm matches that. Pairs with `zipWith` in
-- accept/indexed-families.sw (docs/proposals/indexed-families.md §9, test 16).
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def zipWith (f: a → b → c): Vec a n → Vec b n → Vec c n
  | VNil, VNil => VNil
