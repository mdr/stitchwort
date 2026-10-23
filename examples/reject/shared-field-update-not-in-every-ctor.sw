-- expect-error: E-UNKNOWN-FIELD
-- `text` is only the constructor `Circle`'s, so it cannot be updated through `Shape`.

type Shape =
  | Dot (id: Text) (start: Nat)
  | Circle (id: Text) (start: Nat) (text: Text)

def f (s: Shape): Shape := { s | text = "x" }
