-- expect-error: E-ALGEBRA
-- A coefficient goes before its hypothesis.
import Std (Int)

theorem afterwards (a: Int) (b: Int) (h: a = b): 2 * a = 2 * b := algebra [h * 2]
