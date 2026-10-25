-- expect-error: E-NO-NAMESPACE
-- A function has no namespace for dot notation to look in.

def twice (f: Nat → Nat): Nat := f.size
