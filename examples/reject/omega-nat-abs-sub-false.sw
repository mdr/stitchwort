-- expect-error: E-OMEGA
-- Subtracting can make a number bigger in size: `|x - y| ≤ |x|` fails at
-- `x = 0`, `y = 1`.
import Std (Nat, Int)

theorem absSubLe (x: Int) (y: Int): (x - y).natAbs ≤ x.natAbs := omega
