-- expect-error: E-NOT-A-FUNCTION
-- A type's parameters are implicit in its constructors: `Nil Nat` gives
-- `Nil` an argument it doesn't take. The note shows how to give the
-- parameter by name (D3514).

def noNumbers: List Nat := Nil Nat
