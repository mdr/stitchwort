-- expect-error: E-UNSOLVED
-- Nothing says what kind of list `Nil` is.
zero : Nat
zero = List.length Nil
