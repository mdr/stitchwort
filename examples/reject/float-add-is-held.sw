-- expect-error: E-REFL
-- `Float.add` has a native, so record eta doesn't open its pattern on
-- unknown doubles (D2551): `x + y` isn't its own unfolding by computation,
-- though it is in the model. Without the hold this would check.
import Std (Float)

theorem addUnfolds (x y: Float): Float.add x y = Float.ofBits (Float.Model.addBits x.bits y.bits) := rfl
