-- expect-error: E-TYPE-MISMATCH
-- `<` on `Text` is its `Ord` order, so a numeral, which is a `Nat` or an
-- `Int`, can't be compared with one.
def r (t: Text): Prop := t < 1
