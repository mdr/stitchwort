-- expect-error: E-PARSE
-- A definition's parameter is a name, not a pattern. The note says to name
-- it and take it apart with `let (x, y) := point` (or a `match`); a
-- lambda's parameter can be a pattern (SW-950).

def onDiagonal ((x, y): (Nat, Nat)): Bool := x == y
