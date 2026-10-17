-- expect-error: E-TYPE-MISMATCH
-- A negative number pattern is an `Int`; a `Nat` argument has no negative
-- numbers to match.
f : Nat -> Nat
f (-1) = 1
f _ = 2
