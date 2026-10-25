-- expect-error: E-IMPLICIT-FIELD
-- `i` is used only in the result, so it's an automatic implicit field of
-- type `Fin n`, which mentions the written field `n`. Automatic fields go
-- before the written ones, so it has to be written out. Pairs with `Dep` in
-- accept/indexed-families.sw (docs/proposals/indexed-families.md §9,
-- test 26; D144).
type Fin: Nat → Type =
  | FZero: Fin (Succ n)
  | FSucc (i: Fin n): Fin (Succ n)

type Dep: (n: Nat) → Fin n → Type =
  | Mk (n: Nat): Dep n i
