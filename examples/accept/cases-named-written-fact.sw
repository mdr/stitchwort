-- In `cases x then t`, a hypothesis as written that says a variable is a
-- constructor, `hk: k = C1`, puts `C1` in place of `k`: `k` isn't named, so
-- it is never split, and in the case `d = False` the goal computes only once
-- `k` is known.
import Std (Bool)

type Code = | C0 | C1 | C2

def isC1: Code → Bool
  | C1 => True
  | _ => False

theorem eitherHolds ∀ (d: Bool) (k: Code) (hk: k = C1): (d || isC1 k) = True := cases d then byComputing
