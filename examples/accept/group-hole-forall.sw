-- A group `(x y: _)` is shorthand for `(x: _) (y: _)`: each name gets its
-- own hole, so `x` can be a number and `y` a boolean (D3679).
def p: Prop := ∀ (x y: _) => x + 1 = 2 ∧ y = True
