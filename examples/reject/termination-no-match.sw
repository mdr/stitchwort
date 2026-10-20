-- expect-error: E-TERMINATION
-- No `match`/case tree, so the recursive call is on a non-decreasing
-- argument: the definition never terminates.
def f (n: Nat): Nat := f (n - 1)
