-- expect-error: E-UNKNOWN-NAME
-- `rfl` is written `byComputing` (D3651); `rfl`, `refl` and `Eq.refl` get
-- a note naming it.
import Std (Nat)

theorem two: 1 + 1 = 2 := rfl
