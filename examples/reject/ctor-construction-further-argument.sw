-- expect-error: E-PARSE
-- Braces after a constructor name its fields and take no further arguments.

type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (text: Text)

def c: Shape := Circle { ref = 1, id = "a" } "t"
