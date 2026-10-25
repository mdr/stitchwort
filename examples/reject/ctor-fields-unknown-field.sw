-- expect-error: E-UNKNOWN-FIELD
-- Braces after a constructor name its explicit fields; the error lists them.

type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (text: Text)

def colourOf: Shape → Text
  | Circle { colour, .. } => colour
  | _                     => "none"
