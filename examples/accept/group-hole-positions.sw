-- A group `(x y: _)` is shorthand for `(x: _) (y: _)` in a header and in a
-- function type too: each name gets its own hole, worked out from the
-- parameters after it (D3679).
def f (x y: _) (hx: x = 1) (hy: y = True): Nat := 0

def g: (x y: _) -> x = 1 -> y = True -> Nat := x y hx hy => 0
