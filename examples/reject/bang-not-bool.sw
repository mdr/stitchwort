-- expect-error: E-TYPE-MISMATCH
-- `!` is `Bool.not`: its operand is a `Bool`, not a `Nat`.
def bad (n: Nat): Bool := !n
