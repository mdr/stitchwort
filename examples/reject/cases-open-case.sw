-- expect-error: E-CASES
-- A case that `cases` can't close: the error names the case by the splits that
-- led to it, and shows only that case's own hypotheses.
import Std (Bool, Nat)

theorem atMostTwo (a: Bool) (n: Nat) (h: (a ∧ Nat.leq n 3) = True): n <= 2 := cases
