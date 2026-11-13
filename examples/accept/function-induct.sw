-- Functional induction (docs/proposals/function-equations.md §5, stage 2a):
-- a recursive definition `f` gets `f.induct`, an induction principle with
-- one case for each of its equations (named after it: `f.eq2.ifTrue` is
-- case `eq2IfTrue`), each with an induction hypothesis for every recursive
-- call in the branch, and the motive given `f`'s result (the unfolding
-- form), so no case needs to rewrite with an equation. Leading parameters
-- every call passes on unchanged come first and aren't the motive's.
import Std (Bool, Eq, List, Nat, Option, Or, Void)

-- Structural, with a fixed prefix (`k`) and an `if`: `countAbove.induct k
-- motive eq1 eq2IfTrue eq2IfFalse xs`.
def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

theorem countAboveLe ∀ (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs :=
  countAbove.induct k (xs result => result ≤ List.length xs)
    omega
    (x xs h ih => omega)
    (x xs h ih => omega)
    xs

-- `decreasing`: the proof recurses on the same measure, each call with the
-- decrease proof the definition's has, so the theorem needs none.
def halvings (n: Nat) (count: Nat): Nat
    decreasing n
:=
  if h: n / 2 < n then halvings (n / 2) (count + 1) [decreasing := h] else count

theorem halvingsGe ∀ (n: Nat) (count: Nat): count ≤ halvings n count :=
  halvings.induct (n count result => count ≤ result)
    (n count h ih => omega)
    (n count notH => omega)
    n count

-- A named `match` on a `Bool`: the case has its equation `big`.
def firstBig: List Nat → Option Nat
  | [] => None
  | [x, ..rest] =>
    match big: Nat.leq 10 x with
      | True => Some x
      | False => firstBig rest

theorem firstBigIsBig ∀ (xs: List Nat) (y: Nat): firstBig xs = Some y → Nat.leq 10 y = True :=
  firstBig.induct (xs result => result = Some y → Nat.leq 10 y = True)
    (none => cases)
    (x rest big found => cases)
    (x rest big ih found => ih found)
    xs

-- A `match` on an expression: the case has the alternative's variable and
-- the equation `isSome: List.head rest = Some y`.
def lastOr (d: Nat): List Nat → Nat
  | [] => d
  | [x, ..rest] =>
    match List.head rest with
      | Some y => lastOr y rest
      | None => x

theorem headMem: ∀ (xs: List Nat) (y: Nat) => List.head xs = Some y → List.Mem y xs
  | [], y, h => cases
  | [z, ..zs], y, h => Inl (Option.someInjective h)

theorem lastOrOfMem ∀ (d: Nat) (xs: List Nat): lastOr d xs = d ∨ List.Mem (lastOr d xs) xs :=
  lastOr.induct (d xs result => result = d ∨ List.Mem result xs)
    (d => Inl rfl)
    (d x rest y isSome ih =>
      match ih with
        | Inl same => Inr (Inr (rewrite same in headMem rest y isSome))
        | Inr inRest => Inr (Inr inRest))
    (d x rest isNone => Inr (Inl rfl))
    d xs

-- Two recursive calls, and an arm an earlier one overlaps: case `eq3`
-- takes `notArm2`, which the generated proof establishes at each of the
-- definition's cases it covers.
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

theorem exAtMostTotal ∀ (depth: Nat) (n: Num): ex depth n ≤ total n :=
  ex.induct (depth n result => result ≤ total n)
    (depth value => omega)
    (depth a b h => omega)
    (depth a b h => omega)
    (depth left right notArm2 ih1 ih2 => omega)
    depth n

-- A `_` in a pattern is a case variable like any other, in the order the
-- pattern writes it: `head` then `rest`, as `[x, ..rest]` would give.
def countAll: List Nat → Nat
  | [] => 0
  | [_, ..rest] => Succ (countAll rest)

theorem countAllIsLength ∀ (xs: List Nat): countAll xs = List.length xs :=
  countAll.induct (xs result => result = List.length xs)
    omega
    (head rest ih => omega)
    xs
