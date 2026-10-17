-- expect-error: E-TYPE-MISMATCH
-- `n - -1` has a prefix minus, which forces `Int`, but `n` is a `Nat`.
r : Nat -> Nat
r n = n - -1
