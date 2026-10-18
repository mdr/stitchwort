-- expect-error: E-NOT-A-TYPE
-- A tuple of values isn't a type.
def f : (1, 2) -> Nat
  | _ => 0
