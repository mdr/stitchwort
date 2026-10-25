-- expect-error: E-RECORD-FIELD
-- Each field is named once.

type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (text: Text)

def idOf: Shape → Text
  | Circle { id, id = other, .. } => id
  | Dot { id, .. }                => id
