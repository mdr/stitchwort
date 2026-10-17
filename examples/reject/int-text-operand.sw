-- expect-error: E-TYPE-MISMATCH
-- `<` works on `Nat` and `Int`, not on `Text`.
r : Text -> Prop
r t = t < 1
