-- expect-error: E-TYPE-MISMATCH
-- A `NonEmptyList` literal needs an item of its own: the lists spread into
-- it may all be empty.
import Std (NonEmptyList)

def wrap (xs: List Nat): NonEmptyList Nat := [..xs]
