-- expect-error: E-OMEGA
-- A division by a variable is an unknown number to `omega`; the note names
-- the std facts to hint.
import Std (Nat)

theorem divLeSelf (n: Nat) (k: Nat) (h: k ≠ 0): n / k ≤ n := omega
