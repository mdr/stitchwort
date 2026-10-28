-- expect-error: E-TERMINATION
-- Pairs with accept/termination-list-patterns.sw: in the `[p]` clause, `[p]`
-- rebuilt inside a `match` is the argument itself: `loop [1]` calls
-- `loop [1]` forever.
def loop: List Nat → Nat
  | [] => 0
  | [p] =>
    match p < 3 with
      | True => loop [p]
      | False => 0
  | [p, ..ps] => loop ps
