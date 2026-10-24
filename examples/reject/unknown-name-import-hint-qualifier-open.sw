-- expect-error: E-UNKNOWN-NAME
-- `Effect` is open here, so the library's `Done` is written
-- `Effect.Comp.Done`; the suggested `import` still starts at `Std` (SW-403).
import Std (Effect)

def x: Nat := Done
