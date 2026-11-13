-- `Nat.succInjective`'s `m` and `n` are implicit: the equation `p` fixes them.
import Std (Nat)

theorem predEq ∀ (a: Nat) (b: Nat) (p: Succ a = Succ b): a = b := Nat.succInjective p
