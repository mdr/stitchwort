-- expect-error: E-TERMINATION
-- Pairs with accept/structural-rebuilt-pattern.sw: the list passed on is
-- rebuilt from the pattern's parts, but in a different order, so it isn't
-- the matched list's tail. The error names that argument, not `check`,
-- which is passed on unchanged.
def everyPair (check: Nat → Nat → Bool): (levels: List Nat) → Bool
  | Nil => True
  | Cons x Nil => True
  | Cons x (Cons y more) => check x y && everyPair check (Cons y (Cons x more))
