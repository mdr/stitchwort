-- expect-error: E-REFL
-- `0.1 + 0.2` is the double the checker computes, not 0.3; doubles are shown
-- as their literals.
import Std (Float)

theorem notPointThree: 0.1 + 0.2 = 0.3 := rfl
