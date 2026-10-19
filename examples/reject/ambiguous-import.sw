-- expect-error: E-AMBIGUOUS
-- Two imports bring in `length`: that's fine until `length` is used.
import List (length)
import Text (length)

def count (xs: List Nat): Nat := length xs
