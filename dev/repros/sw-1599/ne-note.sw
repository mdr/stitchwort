import Std (Nat, Eq, Bool, Decidable)

theorem t ∀ (a: Nat) (b: Nat) (h: Decidable.toBool (Nat.decEq a b) = True): a ≠ b ∧ a = a := h
