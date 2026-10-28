-- expect-error: E-RING
-- A coefficient goes before its hypothesis.
import Std (Int)

theorem afterwards (a: Int) (b: Int) (h: a = b): 2 * a = 2 * b := ring [h * 2]
