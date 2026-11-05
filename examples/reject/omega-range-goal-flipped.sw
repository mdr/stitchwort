-- expect-error: E-OMEGA
-- `List.Any (y => x = y) …` is not the membership `x ∈ …` (the equation is the
-- other way round), so omega doesn't take it for a range goal.
import Std (List, Nat)

theorem flipped (x n: Nat) (k: x < n): List.Any (y => x = y) (0 ..< n) := omega
