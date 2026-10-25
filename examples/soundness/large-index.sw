-- expect-error: E-UNIVERSE
-- An index's type obeys the universe bound for fields (D142): `Type` lives
-- in `Type 1`, too large for a family in `Type`, and so is the automatic
-- field `b: Type` of `TList`. Pairs with `Ty: Type -> Type 1` in
-- accept/indexed-families.sw (docs/proposals/indexed-families.md §6.6,
-- test 21).
type Ty: Type → Type =
  | TNat: Ty Nat
  | TList (t: Ty b): Ty (List b)
