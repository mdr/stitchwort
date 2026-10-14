-- expect-error: E-UNKNOWN-NAME
-- `length`'s implicit parameter is called `a`, not `b`.
two : Nat
two = length [b := Nat] [1, 2]
