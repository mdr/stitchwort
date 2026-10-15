-- expect-error: E-MUTUAL-SIGNATURE
-- A type that mentions a definition checked together with it (§6.8,
-- example 16): `g` calls `f`, so they're one group, and `f`'s type can't
-- depend on how `g`, unchecked, computes.
-- Neighbour: `evenNotOdd`/`oddNotEven` in accept/mutual.sw, whose types
-- mention `isEven` and `isOdd`, finished before them.
f : (n : Nat) -> g n = g n
f n = rfl

g : Nat -> Nat
g 0        = 0
g (Succ n) = keep (f n) (g n)

keep : [x y : Nat] -> x = y -> Nat -> Nat
keep _ m = m
