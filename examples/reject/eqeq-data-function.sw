-- expect-error: E-INSTANCE-NONE
-- `==` isn't derived for a type with a function field: functions can't be compared.
type Handler =
  | MkHandler (name: Text) (f: Nat -> Nat)

def same (a: Handler) (b: Handler): Bool := a == b
