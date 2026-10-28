-- expect-error: E-TERMINATION
-- Pairs with accept/termination-list-patterns.sw: after `[p]`, the last
-- clause's list is `Cons p (Cons head tail)`. Rebuilt whole inside the lifted
-- `match`, it is the argument itself, no smaller: `loop [1, 2]` calls
-- `loop [1, 2]` forever.
def loop: List Nat → Nat
  | [] => 0
  | [p] => p
  | [p, ..ps] =>
    match p < 3 with
      | True => loop (Cons p ps)
      | False => 0
