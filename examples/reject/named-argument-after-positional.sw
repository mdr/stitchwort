-- expect-error: E-DUPLICATE-ARGUMENT
-- A call means the same however it's bracketed (D1112): `place 1` has
-- already filled `x`, so `(place 1) (x := 2)` names it again, as
-- `place 1 (x := 2)` does.

def place (x: Nat) (y: Nat): Nat := x * 10 + y

def again: Nat := (place 1) (x := 2)
