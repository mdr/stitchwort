-- expect-error: E-AUTO-STUCK
-- Whether `d` is zero isn't known until the program runs. The fix is
-- `if h: d != 0 then n / d else …`, as in accept/decisions.sw.
def ratio (n: Nat) (d: Nat): Nat := n / d
