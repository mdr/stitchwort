-- P6b. What `down.%step` is, written out (the body with `%rec` for the
-- recursive call, its `match` as a named function): after `down.unfold`,
-- the generator's proof is one `J` with a motive over the scrutinee and its
-- equation together, for any `rec`.
import Std (Bool, Eq, List, Nat, Option, Void)

def downStep (n: Nat) (rec: (m: Nat) → m < n → Nat): (b: Bool) → Nat.leq n 0 = b → Nat
  | True, small => 0
  | False, small => 1 + rec (n - 1) omega

theorem downStepFalse ∀ (n: Nat) (rec: (m: Nat) → m < n → Nat)
    (h: Nat.leq n 0 = False):
    downStep n rec (Nat.leq n 0) rfl = downStep n rec False h :=
  J (y e => downStep n rec (Nat.leq n 0) rfl = downStep n rec y e) rfl h

theorem downStepTrue ∀ (n: Nat) (rec: (m: Nat) → m < n → Nat)
    (h: Nat.leq n 0 = True):
    downStep n rec (Nat.leq n 0) rfl = 0 :=
  J (y e => downStep n rec (Nat.leq n 0) rfl = downStep n rec y e) rfl h
