-- expect-error: E-TERMINATION
-- Each call makes something smaller, but not the same thing, and makes the
-- other thing bigger: `f 1 0 → g 0 1 → f 2 0 → g 1 1 → f 3 0 → …` runs
-- forever (docs/proposals/mutual-recursion.md §6.8, example 11). Merging the
-- two calls' graphs into one would wrongly accept it.
-- Neighbour: `isEven`/`isOdd` in accept/mutual.sw.
f : Nat -> Nat -> Nat
f Zero     y = y
f (Succ x) y = g x (Succ y)

g : Nat -> Nat -> Nat
g x Zero     = x
g x (Succ y) = f (Succ (Succ x)) y
