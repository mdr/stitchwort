-- `omega` reads a `!=` inside a `Bool` hypothesis as a disequation:
-- `(a != b) = True` is `a ≠ b`, and `(a != b) = False` is `a = b`. The
-- `False` case goes through `Decidable.notNotOf`, so the proof stays a few
-- lemma applications that the kernel checks.

import Std (Nat, Int, Bool, Decidable)

theorem natNeTrue ∀ (a b: Nat) (h: ((a != b): Bool) = True) (g: a ≤ b): a < b := omega

theorem natNeFalse ∀ (a b: Nat) (h: ((a != b): Bool) = False) (g: a ≤ b): b ≤ a := omega

theorem intNeTrue ∀ (a b: Int) (h: ((a != b): Bool) = True) (g: a ≤ b): a < b := omega

theorem intNeFalse ∀ (a b: Int) (h: ((a != b): Bool) = False): a ≤ b ∧ b ≤ a := omega

theorem eqFalse ∀ (a b: Nat) (h: (a == b) = False) (g: a ≤ b): a < b := omega
