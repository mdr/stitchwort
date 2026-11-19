-- expect-error: E-TYPE-MISMATCH
-- A definition whose expected type is a synonym: the mismatch names the type
-- as written, not its unfolding.
type Grid = List (List Nat)

def g: Grid := 3
