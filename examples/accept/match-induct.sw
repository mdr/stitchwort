-- `match induct (f args) with` (docs/proposals/function-equations.md §5.3,
-- stage 2b): functional induction (`f.induct`, function-induct.sw) written as
-- a `match`. The motive is the goal with the call abstracted, so it needn't
-- be written; each alternative is named after a case and binds the case's
-- variables, then its hypotheses, then its induction hypotheses, in order
-- (`_` ignores one). Alternatives may come in any order, and all are required.
import Std (Bool, Eq, List, Nat, Option, Or, Void)

def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

-- Function-induct.sw proves this with the motive written out.
theorem countAboveLe (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs := match induct (countAbove k xs) with
  | eq1 => omega
  | eq2IfTrue x xs h ih => omega
  | eq2IfFalse x xs h ih => omega

-- In any order, and `_` for a name that isn't used.
theorem countAboveLe2 (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs := match induct (countAbove k xs) with
  | eq2IfFalse _ _ _ _ => omega
  | eq1 => omega
  | eq2IfTrue _ _ _ _ => omega

def halvings (n: Nat) (count: Nat): Nat
    decreasing n
:=
  if h: n / 2 < n then halvings (n / 2) (count + 1) [decreasing := h] else count

theorem halvingsGe (n: Nat) (count: Nat): count ≤ halvings n count := match induct (halvings n count) with
  | eqIfTrue n count h ih => omega
  | eqIfFalse n count notH => omega

-- Hypotheses that mention the call's variables are generalised: `found`
-- below stays in scope in each alternative, refined (its `xs` is `Nil` in
-- the first, `Cons x rest` in the others), and each `ih` takes it as a
-- premise.
def firstBig: List Nat → Option Nat
  | [] => None
  | [x, ..rest] =>
    match big: Nat.leq 10 x with
      | True => Some x
      | False => firstBig rest

theorem firstBigIsBig (xs: List Nat) (y: Nat) (found: firstBig xs = Some y): Nat.leq 10 y = True :=
  match induct (firstBig xs) with
    | eq1 => cases
    | eq2True x rest big => cases
    | eq2False x rest big ih => ih found

type Num =
  | Reg (value: Nat)
  | Pr (left: Num) (right: Num)

def total: Num → Nat
  | Reg value => value
  | Pr left right => total left + total right

def ex (depth: Nat): Num → Nat
  | Reg _ => 0
  | Pr (Reg a) (Reg b) => if 4 ≤ depth then a + b else 0
  | Pr left right => ex (depth + 1) left + ex (depth + 1) right

theorem exAtMostTotal (depth: Nat) (n: Num): ex depth n ≤ total n := match induct (ex depth n) with
  | eq1 depth value => omega
  | eq2IfTrue depth a b h => omega
  | eq2IfFalse depth a b h => omega
  | eq3 depth left right notArm2 ih1 ih2 => omega

-- A goal that is an implication isn't introduced by the names: the body is a
-- function. (Here the premise isn't a variable in scope, so it isn't
-- generalised; a hypothesis `found` in scope is.)
theorem firstBigIsBigImplies (xs: List Nat) (y: Nat): firstBig xs = Some y → Nat.leq 10 y = True :=
  match induct (firstBig xs) with
    | eq1 => none => cases
    | eq2True x rest big => found => cases
    | eq2False x rest big ih => found => ih found
