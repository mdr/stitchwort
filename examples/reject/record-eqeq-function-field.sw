-- expect-error: E-AUTO-NONE
-- `==` isn't derived for a record with a function field: functions can't be compared.
type Handler = { name: Text, run: Nat -> Nat }

def same (a: Handler) (b: Handler): Bool := a == b
