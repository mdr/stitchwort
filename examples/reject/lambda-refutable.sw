-- expect-error: E-LET-REFUTABLE

import Std (List)

-- A lambda's pattern parameter must cover every value of its type.
def nums (ms: List (Option Nat)): List Nat := List.map ((Some x) => x) ms
