-- expect-error: E-AMBIGUOUS
-- Both `(..)` imports bring `length`: that is fine until it is used.
import List (..)
import Text (..)

def count(xs: List Nat): Nat := length xs
