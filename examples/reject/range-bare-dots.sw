-- expect-error: E-PARSE
-- A range is `a ..< b` or `a ..= b`; a bare `a .. b` is neither.
import Std (List, Nat)

def numbers (n: Nat): List Nat := 1 .. n
