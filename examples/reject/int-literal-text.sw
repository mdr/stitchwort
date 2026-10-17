-- expect-error: E-TYPE-MISMATCH
-- A numeral can be a `Nat` or an `Int`, never a `Text`.
r : Text -> Bool
r t = t == 0
