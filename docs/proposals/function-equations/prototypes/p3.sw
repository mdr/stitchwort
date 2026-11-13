-- P3b. The catch-all's hypothesis as one `∉` of the literals: proving it,
-- and using the equation with it.
import Std (Bool, Eq, List, Nat, Option, Void, byDecision)

def kind: Nat → Nat
  | 3 => 1
  | 7 => 2
  | _ => 0

theorem kindEq3 ∀ (n: Nat) (h: n ∉ [3, 7]): kind n = 0 := match n with
  | 3 => Void.exfalso (h (Inl rfl))
  | 7 => Void.exfalso (h (Inr (Inl rfl)))
  | _ => rfl

-- Expected to fail: neither `omega` (E-OMEGA, model n = 10) nor `cases`
-- (E-CASES) proves `n ∉ [3, 7]` from `10 ≤ n`; one `≠` per number works (p1.sw).
theorem kindUseOmega ∀ (n: Nat) (big: 10 ≤ n): kind n = 0 := kindEq3 n omega

theorem kindUseCases ∀ (n: Nat) (big: 10 ≤ n): kind n = 0 := kindEq3 n cases

type Command = | Up | Down

def commandOf (char: Char): Option Command := match char with
  | 'k' => Some Up
  | 'j' => Some Down
  | _ => None

theorem commandOfEq3 ∀ (char: Char) (h: char ∉ ['k', 'j']): commandOf char = None := match char with
  | 'k' => Void.exfalso (h (Inl rfl))
  | 'j' => Void.exfalso (h (Inr (Inl rfl)))
  | _ => rfl

def keys: List Char := ['k', 'j']

theorem commandUse ∀ (char: Char) (other: char ∉ keys): commandOf char = None := commandOfEq3 char other

theorem commandUseX: commandOf 'x' = None := commandOfEq3 'x' byDecision
