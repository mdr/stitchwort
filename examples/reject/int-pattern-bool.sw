-- expect-error: E-TYPE-MISMATCH
-- A number pattern needs a numeric argument type; `Bool` is not one.
f : Bool -> Nat
f (-1) = 1
f _ = 2
