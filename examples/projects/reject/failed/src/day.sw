-- Uses `f`, which has an error. `g` only refers to it, so it is checked
-- against `f`'s statement, which stands in for it; `gIsZero` must compute
-- `f`, so it can't be checked until `f` is fixed, said once, on the import.
namespace Day

import Lib (f)

def g: Nat := f

theorem gIsZero: g = 0 := rfl
