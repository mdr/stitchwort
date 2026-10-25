-- expect-error: E-OMEGA
-- A division is an unknown number to `omega`; the note names the std facts to hint.
import Std (Nat)

theorem half (n: Nat): n / 2 ≤ n := omega
