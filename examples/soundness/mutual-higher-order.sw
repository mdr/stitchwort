-- expect-error: E-TERMINATION
-- A member of a group passed bare to a helper, which hides what it's called
-- on (§6.8, example 12): refused, because a member must be given all its
-- arguments wherever it's used in the group.
-- Neighbour: `walk`/`stepBy` in accept/mutual.sw, which passes
-- `\x -> stepBy k x` with `k` smaller.
applyTo : (List Nat -> Nat) -> List Nat -> Nat
applyTo f xs = f xs

walk : List Nat -> Nat
walk ts = applyTo walkList ts

walkList : List Nat -> Nat
walkList Nil         = 0
walkList (Cons _ ts) = walk ts
