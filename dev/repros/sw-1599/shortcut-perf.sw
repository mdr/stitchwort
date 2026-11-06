import Std (Nat, Eq)

def fib: Nat → Nat
  | 0 => 0
  | 1 => 1
  | Succ (Succ n) => fib n + fib (Succ n)

def id2 (n: Nat): Nat := n

theorem direct: fib (id2 24) = fib (id2 24) := rfl
theorem viaArgs: fib (id2 24) = fib (id2 (23 + 1)) := rfl
