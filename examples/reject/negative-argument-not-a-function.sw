-- expect-error: E-NOT-A-FUNCTION
-- `n -1`, with a space before the `-` and none after it, is a negative
-- argument, not a subtraction: `n` is not a function.
def h (n: Nat): Nat := n -1
