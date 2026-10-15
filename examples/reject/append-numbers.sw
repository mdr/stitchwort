-- expect-error: E-TYPE-MISMATCH
-- `++` joins texts or lists, not numbers.
bad : Nat
bad = 1 ++ 2
