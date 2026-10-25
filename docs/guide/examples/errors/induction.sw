import Std (Eq)

theorem plusZero: (n: Nat) → n + 0 = n
  | Zero => rfl
  | Succ k => plusZero k
