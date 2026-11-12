-- `Nat.equal`, which `==` on `Nat` computes to, reads as `=` and, when
-- `False`, as `≠`.
import Std (Bool, Nat)

theorem same (m n: Nat) (h: (m == n) = True): m = n := h.read

theorem apart (m n: Nat) (h: (m == n) = False): m ≠ n := h.read

theorem apartApplied (m n: Nat) (h: (m == n) = False) (e: m = n): Void := h.read e

theorem succSame (m n: Nat) (h: Nat.equal (Succ m) (Succ n)): m = n :=
  match h.read with
    | rfl => rfl
