-- expect-error: E-TYPE-MISMATCH
-- A numeral can be a `Nat` or an `Int`, never a `Text`.
def r (t: Text): Bool := t == 0
