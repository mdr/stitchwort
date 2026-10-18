-- expect-error: E-TYPE-MISMATCH
-- A `Nat` and an `Int` can not be mixed; convert with `n.toInt`.
def r (n : Nat) (i : Int) : Bool := n + i == 0
