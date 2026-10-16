-- expect-error: E-DUPLICATE
-- A record whose field type failed to check is left failed, so patterns, literals
-- and projections on it report the real error rather than panicking.
type Dir : Type =
  | L
  | R

type Rot = { dir : Dir, amount : Nat }

f : Rot -> Nat
f { dir = R, amount } = amount
f { dir = L, amount } = 0
