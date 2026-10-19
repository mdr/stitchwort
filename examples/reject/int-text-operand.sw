-- expect-error: E-TYPE-MISMATCH
-- `<` works on `Nat` and `Int`, not on `Text`.
def r (t: Text): Prop := t < 1
