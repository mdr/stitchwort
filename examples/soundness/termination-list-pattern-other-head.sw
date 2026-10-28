-- expect-error: E-TERMINATION
-- Pairs with accept/termination-list-patterns.sw: the tail with a different
-- head is as long as the argument, not a part of it: `loop [1, 2]` calls
-- `loop [0, 2]`, which calls itself forever.
def loop: List Nat → Nat
  | [] => 0
  | [p] => 0
  | [p, ..ps] =>
    match p < 3 with
      | True => loop (Cons 0 ps)
      | False => 0
