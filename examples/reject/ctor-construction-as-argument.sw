-- expect-error: E-PARSE
-- As an argument, a constructor with fields needs brackets.

type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (text: Text)

def d: Option Shape := Some Dot { ref = 1, id = "a" }
