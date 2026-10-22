-- expect-error: E-OMEGA
-- `x <= y` does not give `x < y`: `x = y = 0` is a counterexample.
import Std (Nat)

theorem intModel (x: Nat) (y: Nat) (h: x <= y): x < y := omega
