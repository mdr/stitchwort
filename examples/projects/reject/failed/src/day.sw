-- Uses `f`, which has an error: `g` can't be checked until it's fixed,
-- said once, on the import.
namespace Day

import Lib (f)

def g: Nat := f
