-- expect-error: E-TYPE-MISMATCH
-- `++` joins texts or lists, not numbers.
def bad: Nat := 1 ++ 2
