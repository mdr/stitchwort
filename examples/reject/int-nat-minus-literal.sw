-- expect-error: E-TYPE-MISMATCH
-- `n - -1` has a prefix minus, which forces `Int`, but `n` is a `Nat`.
def r (n : Nat) : Nat := n - -1
