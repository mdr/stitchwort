-- expect-error: E-NO-NAMESPACE
-- A function has no namespace for dot notation to look in.

twice : (Nat -> Nat) -> Nat
twice f = f.size
