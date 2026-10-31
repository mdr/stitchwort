-- expect-error: E-TYPE-MISMATCH
-- A proposition named by a definition hides its equation (SW-845): `Same x y`
-- against `y = x` says what `Same x y` is. (A relation in its own notation,
-- `n < 3` against `n ≤ 3`, gets no note.)

def Same (x: Nat) (y: Nat): Prop := x = y

def wrong (x: Nat) (y: Nat) (h: Same x y): y = x := h
