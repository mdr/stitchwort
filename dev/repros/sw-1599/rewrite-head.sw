import Std (Nat, Eq)

theorem foo ∀ [f: Nat → Nat] (x: Nat) (h: f x = 0): f x = 0 := h

def double (n: Nat): Nat := n + n

theorem use ∀ (h0: double 3 = 0): double 3 + 1 = 1 :=
  rewrite foo in rfl
