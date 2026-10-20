-- expect-error: E-REWRITE-NOTHING
-- `f y` uses the variable `y`, which the goal binds, so it can't be rewritten:
-- `J` can't go under a binder without function extensionality.
theorem bad (f: Nat -> Nat) (g: Nat -> Nat) (h: [n: Nat] -> f n = g n): (y: Nat) -> f y = g y :=
  rewrite h in y => rfl
