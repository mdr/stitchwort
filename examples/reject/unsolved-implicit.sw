-- expect-error: E-UNSOLVED

import Std (List)

-- Nothing says what kind of list `Nil` is.
def zero: Nat := List.length Nil
