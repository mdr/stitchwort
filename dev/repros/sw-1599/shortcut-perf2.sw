import Std (Nat, Eq)

def fib: Nat → Nat
  | 0 => 0
  | 1 => 1
  | Succ (Succ n) => fib n + fib (Succ n)

def id2 (n: Nat): Nat := n

def heavy (n: Nat): Nat := fib 27 + n

theorem viaArgs ∀ (k: Nat): heavy (id2 (k + 1)) = heavy (id2 (Succ k)) := rfl
