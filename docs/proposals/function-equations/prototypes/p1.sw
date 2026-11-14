-- Prototypes for docs/proposals/function-equations.md (SW-1028).
-- Each theorem is the statement and proof the generator would produce,
-- written by hand.
import Std (Bool, Eq, List, Nat, Option, Void)

-- P1. An overlapping arm (2021 day 18's explode, cut down).
type Num = | Reg (value: Nat) | Pr (left: Num) (right: Num)

def ex (depth: Nat): Num → Nat
  | Reg _ => 0
  | Pr (Reg a) (Reg b) => if 4 ≤ depth then a + b else 0
  | Pr left right => ex (depth + 1) left + ex (depth + 1) right

-- `ex.eq3`: the earlier arm's failure as a hypothesis (Lean's form).
theorem exEq3 ∀ (depth: Nat) (left right: Num) (h: (a: Nat) → (b: Nat) → left = Reg a → right = Reg b → Void):
    ex depth (Pr left right) = ex (depth + 1) left + ex (depth + 1) right :=
  match left, right with
    | Reg a, Reg b => Void.exfalso (h a b rfl rfl)
    | Reg a, Pr x y => rfl
    | Pr x y, r => rfl

-- Using it where the left part is known to be a pair: `cases` discharges the hypothesis.
theorem exUse ∀ (depth: Nat) (x y r: Num): ex depth (Pr (Pr x y) r) = ex (depth + 1) (Pr x y) + ex (depth + 1) r :=
  exEq3 depth (Pr x y) r cases

-- And where nothing is known but a hypothesis about the left part.
def isReg: Num → Bool
  | Reg _ => True
  | Pr _ _ => False

theorem exUse2 ∀ (depth: Nat) (left right: Num)
    (notReg: isReg left = False):
    ex depth (Pr left right) = ex (depth + 1) left + ex (depth + 1) right :=
  exEq3 depth left right (a b el er => Bool.trueNotFalse (rewrite el at notReg in notReg))

-- P3. Literal patterns: the catch-all's equation, with `≠` hypotheses.
type Command = | Up | Down

def commandOf (char: Char): Option Command := match char with
  | 'k' => Some Up
  | 'j' => Some Down
  | _ => None

theorem commandOfEq3 ∀ (char: Char) (h1: char ≠ 'k') (h2: char ≠ 'j'): commandOf char = None := match char with
  | 'k' => Void.exfalso (h1 rfl)
  | 'j' => Void.exfalso (h2 rfl)
  | _ => rfl

def kind: Nat → Nat
  | 3 => 1
  | 7 => 2
  | _ => 0

theorem kindEq3 ∀ (n: Nat) (h1: n ≠ 3) (h2: n ≠ 7): kind n = 0 := match n with
  | 3 => Void.exfalso (h1 rfl)
  | 7 => Void.exfalso (h2 rfl)
  | _ => rfl

theorem kindUse ∀ (n: Nat) (big: 10 ≤ n): kind n = 0 := kindEq3 n omega omega
