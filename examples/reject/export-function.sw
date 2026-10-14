-- expect-error: E-EXPORT
-- Functions can't cross the JS boundary yet.
export
twice : (Nat -> Nat) -> Nat -> Nat
twice f n = f (f n)
