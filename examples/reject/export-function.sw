-- expect-error: E-EXPORT
-- Functions can't cross the JS boundary yet.
export def twice (f: Nat -> Nat) (n: Nat): Nat := f (f n)
