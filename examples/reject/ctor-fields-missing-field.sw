-- expect-error: E-RECORD-FIELD
-- Without `..`, every explicit field is named.

type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (text: Text)

def idOf: Shape → Text
  | Circle { id, text } => id
  | Dot { id, .. }      => id
