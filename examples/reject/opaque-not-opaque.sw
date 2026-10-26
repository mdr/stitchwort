-- expect-error: E-NOT-OPAQUE
-- A definition that isn't opaque always unfolds, so it has no place in an
-- `unfolding` clause. (docs/proposals/opaque-definitions.md §6.10.)
import Std (Nat)

def double (n: Nat): Nat := n + n

theorem doubleThree: double 3 = 6 unfolding double := rfl
