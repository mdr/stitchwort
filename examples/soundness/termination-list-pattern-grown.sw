-- expect-error: E-TERMINATION
-- Pairs with accept/termination-list-patterns.sw: the matched head put back
-- twice around the tail, inside the lifted `match`, is bigger than the
-- argument: `grow [1, 2]` calls `grow [1, 1, 2]`, and so on forever.
def grow: List Nat → Nat
  | [] => 0
  | [p] => 0
  | [p, ..ps] =>
    match p < 3 with
      | True => grow (Cons p (Cons p ps))
      | False => 0
