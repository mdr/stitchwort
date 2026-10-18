-- expect-error: E-UNKNOWN-NAME
-- `List.length`'s implicit parameter is called `a`, not `b`.
def two : Nat := List.length [b := Nat] [1, 2]
