import Std (Nat, Eq)

opaque def wrap (n: Nat): Nat := n

def double (n: Nat): Nat := n + n

opaque def wrap2 (n: Nat) (m: Nat): Nat := n

theorem t1: wrap (double 2) = wrap (double 2) := rfl
theorem t2: wrap (double 2) = wrap (double (1 + 1)) := rfl
theorem t3: wrap (double 2) = wrap (Nat.add 1 3) := rfl
theorem t4: wrap (wrap (double 2)) = wrap (wrap (Nat.add 1 3)) := rfl
theorem t5: wrap2 (wrap (double 2)) 0 = wrap2 (wrap (Nat.add 3 1)) 0 := rfl
theorem t6 ∀ (x: Nat) (h: wrap (double x) = 0): wrap (x + x) = 0 := h
theorem t7 ∀ (x: Nat) (h: wrap (wrap (double x)) = 0): wrap (wrap (x + x)) = 0 := h
