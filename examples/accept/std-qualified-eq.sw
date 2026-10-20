-- `Std.Eq.sym` works without any import; so does dot notation.
theorem flip (a: Nat) (b: Nat) (p: a = b): b = a := Std.Eq.sym p

theorem flipDot (a: Nat) (b: Nat) (p: a = b): b = a := p.sym
