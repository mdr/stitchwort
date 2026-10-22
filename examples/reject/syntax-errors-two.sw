-- expect-error: E-PARSE
-- Two independent syntax errors: both are reported, not just the first.
def f (xs: List Nat): Nat := xs.

def ok: Nat := 1

def g (n: Nat): Nat := (n +
