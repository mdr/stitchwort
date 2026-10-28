-- expect-error: E-TERMINATION
-- Pairs with accept/termination-list-patterns.sw: rebuilt from the pattern's
-- parts in a different order inside the lifted `match`, the list is as long
-- as the argument: `swap [1, 2]` calls `swap [2, 1]`, which calls
-- `swap [1, 2]`, forever.
def swap: List Nat → Nat
  | [] => 0
  | [a] => 0
  | [a, b, ..rest] =>
    match a < 5 with
      | True => swap (Cons b (Cons a rest))
      | False => 0
