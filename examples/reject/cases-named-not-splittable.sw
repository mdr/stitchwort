-- expect-error: E-CASES
-- An equation isn't data, an `∨` or a `Bool`, so it can't be split; the
-- error says why at the name.
import Std (Nat)

theorem atMostThree ∀ (n: Nat) (h: n = 3): n ≤ 3 := cases h then arithmetic
