-- Probe for docs/proposals/bool-and-prop.md §2.3. Each `rfl` here FAILS
-- today (E-REFL): a decision is `Yes proof | No refutation`, so its `Bool`
-- is stuck until the decision is a constructor.
import Std (Bool, Decidable, Nat)

theorem one ∀ (a b: Nat): Decidable.toBool (Nat.decLessEq a b) = Nat.leq a b := rfl
theorem and ∀ (a b c d: Nat):
    Decidable.toBool (Decidable.and (Nat.decLessEq a b) (Nat.decLessEq c d)) = (Nat.leq a b && Nat.leq c d) :=
  rfl
theorem eq ∀ (a b: Nat): (a == b) = Nat.equal a b := rfl
