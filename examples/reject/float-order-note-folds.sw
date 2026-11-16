-- expect-error: E-REFL
-- An unfolded `Float` order comparison is shown as the comparison, `x <=
-- 0.0` and `x < 0.0`, not as the `Int` order keys it computes to (SW-3426).
import Std (Float)

theorem leqBad ∀ (x: Float): Float.leq x 0.0 = True := byComputing

theorem lessBad ∀ (x: Float): Float.less x 0.0 = True := byComputing
