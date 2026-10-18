-- expect-error: E-TYPE-MISMATCH
-- `not` is on `Bool`s, and `x < y` is a proposition: write
-- `if x < y then b else a`, or `if y <= x`.
def atLeast (x : Nat) (y : Nat) : Nat := if not (x < y) then x else y
