-- expect-error: E-MUTUAL-KIND
-- A data type whose constructor uses a definition that's defined with it:
-- induction-recursion, which isn't supported (§7.5).
type Code: Type =
  | Small
  | Join (a: Code) (b: Decode a)

def Decode: Code -> Type
  | Small    => Nat
  | Join a b => Code
