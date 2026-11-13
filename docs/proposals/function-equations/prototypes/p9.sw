-- P9. `rewrite` with an overlap equation where the call is stuck on a
-- variable, and with a transparent constructor arm (a no-op).
import Std (Bool, Eq, List, Nat, Option, Void)

type Num = | Reg (value: Nat) | Pr (left: Num) (right: Num)

def ex (depth: Nat): Num → Nat
  | Reg _ => 0
  | Pr (Reg a) (Reg b) => if 4 ≤ depth then a + b else 0
  | Pr left right => ex (depth + 1) left + ex (depth + 1) right

theorem exEq3 ∀ (depth: Nat) (left: Num) (right: Num) (h: (a: Nat) → (b: Nat) → left = Reg a → right = Reg b → Void):
    ex depth (Pr left right) = ex (depth + 1) left + ex (depth + 1) right := match left, right with
      | Reg a, Reg b => Void.exfalso (h a b rfl rfl)
      | Reg a, Pr x y => rfl
      | Pr x y, r => rfl

theorem exEq1 ∀ (depth: Nat) (v: Nat): ex depth (Reg v) = 0 := rfl

-- The goal is stuck on `left`, so `rewrite` finds the call.
theorem exAtLeast ∀ (depth: Nat) (left: Num) (right: Num) (h: (a: Nat) → (b: Nat) → left = Reg a → right = Reg b → Void):
    ex (depth + 1) left ≤ ex depth (Pr left right) :=
  rewrite exEq3 depth left right h in omega

-- A transparent constructor arm: the goal has already computed it.
theorem exReg ∀ (depth: Nat) (v: Nat) (n: Nat): ex depth (Reg v) + n = n :=
  rewrite exEq1 depth v in rfl
