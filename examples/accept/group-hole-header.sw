-- A theorem's header group `(x y: _)` is shorthand for `(x: _) (y: _)`:
-- the hypotheses settle each name's type on its own (D3679).
theorem t ∀ (x y: _) (hx: x = 1) (hy: y = True): x = 1 := hx
