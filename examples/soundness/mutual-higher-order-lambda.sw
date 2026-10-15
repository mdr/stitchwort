-- expect-error: E-TERMINATION
-- The same, written with a lambda so every call has its arguments: the call
-- `walkList x` is on the lambda's `x`, which isn't known to be smaller than
-- anything, so going round `walk → walkList → walk` nothing gets smaller.
-- (`walk Nil` would loop.)
-- Neighbour: `walk`/`stepBy` in accept/mutual.sw.
applyTo : (List Nat -> Nat) -> List Nat -> Nat
applyTo f xs = f xs

walk : List Nat -> Nat
walk ts = applyTo (\x -> walkList x) ts

walkList : List Nat -> Nat
walkList Nil         = walk Nil
walkList (Cons _ ts) = walk ts
