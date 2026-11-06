-- expect-error: E-TYPE-MISMATCH
-- expect-warning: W-MATCH-NOT-FOUND
-- A named `match` on an expression the goal doesn't contain refines nothing,
-- so an arm that relied on the refinement fails with an error about the arm,
-- not about the `match`. The warning, given with the error, says where the
-- cause is (SW-1485).
import Std (Nat)

def double (n: Nat): Nat := n + n

theorem bad (n: Nat): double n = n + n :=
  match h: n * 2 with
    | Zero => rfl
    | Succ k => Nat.succNotZero k
