-- expect-error: E-NOT-A-RECORD
-- `Circle` is declared with its fields in brackets, so braces after it are
-- its first argument (a `Text`), not its fields. The note says how to name
-- fields: `Circle (id := …)`, or declare it `| Circle { … }`.

type Shape = | Circle (id: Text) (radius: Nat)

def c: Shape := Circle { id = "a", radius = 1 }
