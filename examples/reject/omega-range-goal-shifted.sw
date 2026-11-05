-- expect-error: E-OMEGA
-- `List.Any (y => y + 1 = x) …` is not a membership: its left side is not the
-- element itself, so omega doesn't take it for a range goal.
import Std (List, Nat)

theorem shifted (x n: Nat) (k: x < n): List.Any (y => y + 1 = x) (0 ..< n) := omega
