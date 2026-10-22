-- expect-error: E-OMEGA
-- A literal factor above 1000 on the left is refused, as it would make the proof too big.
import Std (Nat)

theorem big2 (x: Nat) (h: 2000 * x <= 4000): x <= 2 := omega
