-- expect-error: E-TYPE-MISMATCH
-- A negative literal is an `Int`; `Nat` has no negative numbers.
def r: Nat := -1
