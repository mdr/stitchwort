-- expect-error: E-PARSE
-- A range has two ends; `a ..< b ..< c` has no meaning.
import Std (List, Nat)

def numbers (a b c: Nat): List Nat := a ..< b ..< c
