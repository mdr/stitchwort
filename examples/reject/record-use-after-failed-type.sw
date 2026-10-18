-- expect-error: E-DUPLICATE
-- Literals, projections and updates of a record that failed to check.
-- (`Dir` declares `L` twice, so it fails, and `Rot` with it.)
type Dir : Type =
  | L
  | R
  | L

type Rot = { dir : Dir, amount : Nat }

def mk (n : Nat) : Rot := { dir = R, amount = n }

def get (r : Rot) : Nat := r.amount

def bump (r : Rot) : Rot := { r | amount = 1 }

def g : Rot -> Nat
  | { amount, .. } => amount
