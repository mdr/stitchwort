-- Replacing `spare n` with `False` in the goal lets `kept` compute, which
-- uncovers another `spare n` that wasn't there to find when the `match`
-- started. `byComputing` rewrites it along the `match`'s equation and
-- tries again (SW-3741).
import Std (Bool, Nat, Option)

def spare (n: Nat): Bool := 10 < n
def drop (n: Nat): Option Nat := if spare n then None else Some n
def kept (x: Option Nat): Bool := match x with
  | Some n => not (spare n)
  | None => True

theorem keptAfter ∀ (n: Nat): kept (drop n) = True := match isSpare: spare n with
  | True => byComputing
  | False => byComputing

-- Unnamed, the `match` gets its equation when the arm needs it.
theorem keptUnnamed ∀ (n: Nat): kept (drop n) = True := match spare n with
  | True => byComputing
  | False => byComputing
