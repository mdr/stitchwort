import Std (Bool, Nat)

theorem flagged ∀ (flag: Bool) (n: Nat) (h: flag = True): n = n := match h with | Both a b => rfl
