-- expect-error: E-TERMINATION
-- The argument grows instead of shrinking, so this never terminates.
def grow (n : Nat) : Nat := grow (Succ n)
