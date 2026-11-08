-- expect-error: E-TYPE-MISMATCH
-- A lambda with no result type keeps its comparison a proposition, so the
-- mapped list is a `List Prop` and a `List Bool` is refused; the note says
-- how to ask for a `Bool` (SW-2343).
def flags (xs: List Nat): List Bool :=
  let marked := xs.map (n => 9 < n)
  marked
