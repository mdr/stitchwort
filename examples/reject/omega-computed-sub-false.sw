-- expect-error: E-OMEGA
-- `(n + 1).toInt - 2` is `n.toInt - 1`, not `n.toInt`: `omega` reads the
-- `Int.subNatNatFrom (n + 1) 2 (1 - n)` it computes to as that subtraction
-- (SW-997), and still finds the counterexample `n = 0`.
import Std (Int, Nat)

theorem predTwice (n: Nat): (n + 1).toInt - 2 = n.toInt := omega
