-- expect-error: E-UNKNOWN-FIELD
-- Braces name the constructor's own fields.

type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (text: Text)

def c: Shape := Circle { ref = 1, id = "a", text = "t", colour = "red" }
