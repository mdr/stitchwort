-- expect-error: E-DUPLICATE
-- Literals, projections and updates of a record that failed to check.
-- (`Dir` declares `L` twice, so it fails, and `Rot` with it.)
type Dir : Type =
  | L
  | R
  | L

type Rot = { dir : Dir, amount : Nat }

mk : Nat -> Rot
mk n = { dir = R, amount = n }

get : Rot -> Nat
get r = r.amount

bump : Rot -> Rot
bump r = { r | amount = 1 }

g : Rot -> Nat
g { amount, .. } = amount
