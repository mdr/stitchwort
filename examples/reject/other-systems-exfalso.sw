-- expect-error: E-UNKNOWN-NAME
-- Lean's `False.elim` (and the old `Void.exfalso`) is `h.impossible`
-- (D3652).
import Std (Nat)

theorem anything (h: Void): 1 = 2 := False.elim h
