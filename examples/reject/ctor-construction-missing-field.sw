-- expect-error: E-RECORD-FIELD
-- Every explicit field is given.

type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (text: Text)

def c: Shape := Circle { ref = 1, id = "a" }
