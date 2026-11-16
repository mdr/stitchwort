-- expect-error: E-ARITHMETIC
-- An `Int` may be negative: `x ≤ x + y` fails at `y = -1`, though it holds
-- for a `Nat` `y`.
import Std (Int)

theorem addLe (x: Int) (y: Int): x ≤ x + y := arithmetic
