-- expect-error: E-DUPLICATE
-- Literals, projections and updates of a record that failed to check.
type Dir : Type =
  | L
  | R

type Rot = { dir : Dir, amount : Nat }

mk : Nat -> Rot
mk n = { dir = R, amount = n }

get : Rot -> Nat
get r = r.amount

bump : Rot -> Rot
bump r = { r | amount = 1 }

g : Rot -> Nat
g { amount, .. } = amount
