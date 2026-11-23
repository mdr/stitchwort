-- expect-error: E-UNKNOWN-NAME
-- A definition whose body is a guard has equations named for its branches
-- (`pick.eq.ifTrue`, `pick.eq.ifFalse`), not numbers; asking for one that
-- isn't there lists the ones it has, not "no equations".
import Std (Nat)

def pick (n: Nat): Nat := if h: 0 < n then n else 0

theorem pickPositive ∀ (n: Nat) (h: 0 < n): pick n = n := pick.eq1 n h
