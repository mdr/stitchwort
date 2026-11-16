-- expect-error: E-ALGEBRA
-- The wrong coefficient: the message shows what is left over.
import Std (Int)

theorem halfScaled (a: Int) (b: Int) (h: a = 2 * b): 4 * a = 8 * b := algebra [2 * h]
