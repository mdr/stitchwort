-- expect-error: E-AUTO-NONE
-- `==` isn't derived for a type with a proof field, which it can't compare.
type Small =
  | MkSmall (n : Nat) (small : Nat.leq n 10 = True)

same : Small -> Small -> Bool
same a b = a == b
