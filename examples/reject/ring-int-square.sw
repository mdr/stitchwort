-- expect-error: E-RING
-- Over Int the cross terms do not cancel.
import Std (Int)

theorem square (a: Int) (b: Int): (a + b) * (a + b) = a * a + b * b := ring
