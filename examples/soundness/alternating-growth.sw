-- expect-error: E-TERMINATION
-- Each call makes one argument smaller but grows the other, and the two
-- calls take turns: `bounce 1 0` calls `bounce 0 2`, then `bounce 3 1`,
-- `bounce 2 3`, … forever. Combining what each call shrinks, as if one call
-- did both, would wrongly accept it (docs/proposals/mutual-recursion.md
-- §6.5: calls are never merged). Pairs with `ack` in accept/size-change.sw.
bounce : Nat -> Nat -> Nat
bounce Zero     Zero     = 0
bounce (Succ x) y        = bounce x (Succ (Succ y))
bounce Zero     (Succ y) = bounce (Succ (Succ y)) y
