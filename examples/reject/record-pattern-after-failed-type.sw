-- expect-error: E-DUPLICATE
-- A record whose field type failed to check is left failed, so patterns, literals
-- and projections on it report the real error rather than panicking.
-- (`Dir` declares `L` twice, so it fails, and `Rot` with it.)
type Dir: Type =
  | L
  | R
  | L

type Rot = { dir: Dir, amount: Nat }

def f: Rot -> Nat
  | { dir = R, amount } => amount
  | { dir = L, amount } => 0
