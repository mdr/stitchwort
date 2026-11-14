-- expect-error: E-REWRITE-NOTHING
-- The goal has the rule's left side `f a`, but `rewrite <- h` looks for the
-- right side `g a`. It also has `g y` under the function's binder, where
-- `rewrite` can't go: the direction is the mistake, so its note comes first
-- and the notes about searching inside functions are left out.
theorem bad ∀ (f: Nat → Nat) (g: Nat → Nat) (a: Nat) (h: f a = g a):
    (∀ (y: Nat) => g y = g y) → f a = f a :=
  rewrite <- h in rfl
