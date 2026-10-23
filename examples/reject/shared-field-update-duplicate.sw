-- expect-error: E-RECORD-FIELD
-- `id` is given twice.

type Shape =
  | Dot (id: Text) (start: Nat)
  | Circle (id: Text) (start: Nat) (text: Text)

def f (s: Shape): Shape := { s | id = "a", id = "b" }
