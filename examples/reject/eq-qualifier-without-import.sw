-- expect-error: E-UNKNOWN-NAME
-- `Eq` is a library namespace but not a default name: it needs
-- `import Std (Eq)`, or `Std.Eq.sym` (the error says so).
theorem flip (a: Nat) (b: Nat) (p: a = b): b = a := Eq.sym p
