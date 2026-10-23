-- expect-error: E-TYPE-MISMATCH
-- `*` on `Float` isn't there yet.
import Std (Float)

def twice (t: Float): Float := 2 * t
