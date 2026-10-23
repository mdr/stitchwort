-- expect-error: E-UNKNOWN-FIELD
-- `colour` is no field of `Shape` at all.

type Shape =
  | Dot (id: Text) (start: Nat)
  | Circle (id: Text) (start: Nat) (text: Text)

def f (s: Shape): Shape := { s | colour = "x" }
