import Std (Eq)

theorem timesOne ∀ (n: Nat): n * 1 = n := match n with
  | Zero => rfl
  | Succ k => ?
