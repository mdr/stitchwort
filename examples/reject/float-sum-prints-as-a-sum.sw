-- expect-error: E-REFL
-- A `Float` sum prints as a sum, `x + y`, not as the dot call `x.add y`
-- (SW-1763).
import Std (Float)

theorem sumIsSum (x y: Float): x + y = y + x := rfl
