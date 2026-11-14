-- P6. 2024 day 12's shape: a `decreasing` definition whose named `match`
-- on a `Bool` gives the decrease. By hand, every way of stepping through it
-- fails (expected: E-REWRITE-MOTIVE, E-MATCH-MOTIVE, E-MATCH-MOTIVE); the
-- generator's proof is `f.unfold`, then one `J` (p6b.sw).
import Std (Bool, Eq, List, Nat, Option, Void)

def down (n: Nat): Nat
    decreasing n
:=
  match small: Nat.leq n 0 with
    | True => 0
    | False => 1 + down (n - 1) [decreasing := omega]

theorem downRewrite ∀ (n: Nat) (h: Nat.leq n 0 = False): down n = 1 + down (n - 1) := rewrite down.unfold n, h in rfl

theorem downMatch ∀ (n: Nat) (h: Nat.leq n 0 = False): down n = 1 + down (n - 1) :=
  rewrite down.unfold n in
    match e: Nat.leq n 0 with
      | True => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym e) h))
      | False => rfl

theorem downCases ∀ (n: Nat) (h: Nat.leq n 0 = False): down n = 1 + down (n - 1) := rewrite down.unfold n in cases
