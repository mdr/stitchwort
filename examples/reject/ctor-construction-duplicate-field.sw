-- expect-error: E-RECORD-FIELD
-- Each field is given once.

type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (text: Text)

def c: Shape := Circle { ref = 1, id = "a", text = "t", ref = 2 }
