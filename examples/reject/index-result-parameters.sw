-- expect-error: E-TYPE-MISMATCH
-- A constructor's result has the type's own parameters, as declared: only
-- the indices may differ. `Weird: Vec Nat 0` in `Vec (a: Type)` isn't one.
-- Pairs with `VNil: Vec a 0` in accept/indexed-families.sw
-- (docs/proposals/indexed-families.md §9, test 10).
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | Weird: Vec Nat 0
