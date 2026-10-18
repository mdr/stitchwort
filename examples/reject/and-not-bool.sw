-- expect-error: E-TYPE-MISMATCH
-- An operand of `&&` must be a `Bool` or a proposition; `x` is a `Nat`.
def f (x : Nat) : Bool := x && True
