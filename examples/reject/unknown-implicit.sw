-- expect-error: E-UNKNOWN-NAME
-- `List.length`'s implicit parameter is called `a`, not `b`.
two : Nat
two = List.length [b := Nat] [1, 2]
