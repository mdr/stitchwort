-- expect-error: E-OMEGA
-- `(a - b) + b = a` needs `b <= a`: with `a = 0` and `b = 1` the left side is 1.
import Std (Nat)

theorem subAdd (a: Nat) (b: Nat): (a - b) + b = a := omega
