-- expect-error: E-OMEGA
-- `x ∈ 0 ..< n` gives `x < n`, not `x + 1 < n`: omega lists the range's bounds
-- among the facts it used and finds `x = 0, n = 1`.
import Std (List, Nat)

theorem tooMuch (x n: Nat) (h: x ∈ 0 ..< n): x + 1 < n := omega
