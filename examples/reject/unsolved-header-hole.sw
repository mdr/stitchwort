-- expect-error: E-UNSOLVED
-- A `_` in a declaration's type is checked before the body, so neither the
-- body nor a named argument can fill it (SW-2850).

import Std (List)

def mynil: List _ := Nil
