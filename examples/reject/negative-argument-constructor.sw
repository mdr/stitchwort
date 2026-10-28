-- expect-error: E-NOT-A-FUNCTION
-- `Some 5 -1` gives `Some` a second argument, `(-1)`.
import Std (Option)

def h: Option Int := Some 5 -1
