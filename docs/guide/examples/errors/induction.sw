import Std (Eq)

theorem timesOne: (n: Nat) → n * 1 = n
  | Zero => rfl
  | Succ k => timesOne k
