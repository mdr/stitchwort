import Std (Nat, Eq, Bool, Decidable)

theorem t ∀ (a b: Nat) (h: Decidable.toBool (Nat.decEq a b) = True): a ≠ b ∧ a = a := h
