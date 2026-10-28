-- expect-error: E-PARSE
-- A keyword can't be a lambda's parameter.
import Std (Bool, List, Nat)

def keep (xs: List Nat) (property: Nat -> Bool): List Nat := xs.filter (test => property test)
