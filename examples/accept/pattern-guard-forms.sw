-- A guard's hypotheses take the form its condition is written in (D3699):
-- a condition written as a `Bool` gives `c = True` in its arm's case and
-- `c = False` below it; one written as a proposition gives `P` and `¬P`.
-- `&&` isn't split: `.read` gives the conjunction.
import Std (Bool, Eq, List, Nat, Void)

-- A `Bool`: `==` and `&&`.
def countPairs: List Nat → Nat
  | [] => 0
  | [x, y, ..rest] if x == y && x < 5 => 1 + countPairs rest
  | [_, ..rest] => countPairs rest

-- The same test written as a proposition: `x = y` decided.
def countSame: List Nat → Nat
  | [] => 0
  | [x, y, ..rest] if x = y => 1 + countSame rest
  | [_, ..rest] => countSame rest

-- `countPairs.eq2` takes `(x == y && x < 5) = True`, `countSame.eq2` takes `x = y`.
theorem pairsStep ∀ (x y: Nat) (rest: List Nat)
    (guard: (x == y && x < 5) = True):
    countPairs [x, y, ..rest] = 1 + countPairs rest :=
  countPairs.eq2 x y rest guard

theorem sameStep ∀ (x y: Nat) (rest: List Nat) (guard: x = y): countSame [x, y, ..rest] = 1 + countSame rest :=
  countSame.eq2 x y rest guard

-- The guard's conjunction is `guard.read`; one side is `guard.left`.
theorem pairsGuardRead ∀ (x y: Nat) (guard: (x == y && x < 5) = True): (x == y) = True ∧ x < 5 := guard.read

theorem pairsGuardLeft ∀ (x y: Nat) (guard: (x == y && x < 5) = True): (x == y) = True := guard.left

-- Below the guarded arm, where its patterns match only some of the values,
-- the hypothesis ends `… = False` for the `Bool` and `head ≠ y` for the
-- proposition. Each passes straight to the arm's equation.
theorem pairsCases ∀ (xs: List Nat): countPairs xs ≤ xs.length := match induct (countPairs xs) with
  | eq1 => arithmetic
  | eq2 x y rest guard ih => arithmetic
  | eq3 head rest notArm2 ih => arithmetic

theorem pairsOther ∀ (head: Nat) (rest: List Nat)
    (notArm2: ∀ (y: Nat) (rest1: List Nat) => rest = [y, ..rest1] → (head == y && head < 5) = False):
    countPairs [head, ..rest] = countPairs rest :=
  countPairs.eq3 head rest notArm2

theorem sameOther ∀ (head: Nat) (rest: List Nat)
    (notArm2: ∀ (y: Nat) (rest1: List Nat) => rest = [y, ..rest1] → ¬(head = y)):
    countSame [head, ..rest] = countSame rest :=
  countSame.eq3 head rest notArm2

-- Applied to the next value, the `Bool` form is the `= False` fact itself.
theorem pairsOtherNext ∀ (head y: Nat) (rest1: List Nat)
    (notArm2: ∀ (y1: Nat) (rest2: List Nat) => [y, ..rest1] = [y1, ..rest2] → (head == y1 && head < 5) = False):
    (head == y && head < 5) = False :=
  notArm2 y rest1 byComputing

-- A comparison whose proof the arm uses is tested by `Decidable.elim`,
-- and is still a `Bool`: below it, over a partial overlap, `(head < y) =
-- False`. The case's hypothesis passes to a lemma stated as `gaps.eq2`
-- states it.
def gap (x y: Nat) [auto h: x < y]: Nat := y - x

def gaps: List Nat → Nat
  | [x, y, ..rest] if x < y => gap x y + gaps rest
  | [_, ..rest] => gaps rest
  | [] => 0

theorem gapsSkip ∀ (head: Nat) (rest: List Nat)
    (notArm1: ∀ (y: Nat) (rest1: List Nat) => rest = [y, ..rest1] → (head < y) = False):
    gaps [head, ..rest] = gaps rest :=
  gaps.eq2 head rest notArm1

theorem gapsCases ∀ (xs: List Nat): gaps xs ≥ 0 := match induct (gaps xs) with
  | eq1 x y rest guard ih => arithmetic
  | eq2 head rest notArm1 ih =>
    let skip := gapsSkip head rest notArm1
    arithmetic
  | eq3 => arithmetic

-- `if h: P` names a proposition, so it stays one: `¬(head ≤ limit)`.
def firstFits (limit: Nat): List Nat → Nat
  | [x, _, ..rest] if h: x <= limit => x + firstFits limit rest
  | [_, ..rest] => firstFits limit rest
  | [] => 0

theorem firstFitsSkip ∀ (limit head: Nat) (rest: List Nat)
    (notArm1: ∀ (head1: Nat) (rest1: List Nat) => rest = [head1, ..rest1] → ¬(head ≤ limit)):
    firstFits limit [head, ..rest] = firstFits limit rest :=
  firstFits.eq2 limit head rest notArm1

theorem firstFitsCases ∀ (limit: Nat) (xs: List Nat): firstFits limit xs ≥ 0 := match induct (firstFits limit xs) with
  | eq1 x head rest h ih => arithmetic
  | eq2 head rest notArm1 ih =>
    let skip := firstFitsSkip limit head rest notArm1
    arithmetic
  | eq3 => arithmetic

-- Two columns, both partial, the condition using a variable from each:
-- `notArm1` takes both equations and ends `(b == c) = False`.
def pairUp: List Nat → List Nat → Nat
  | [_, b, ..xs], [c, ..ys] if b == c => 1 + pairUp xs ys
  | [_, ..xs], ys => pairUp xs ys
  | [], _ => 0

theorem pairUpSkip ∀ (head: Nat) (xs ys: List Nat)
    (notArm1: ∀ (b: Nat) (xs1: List Nat) (c: Nat) (ys1: List Nat) => xs = [b, ..xs1]
      → ys = [c, ..ys1]
      → (b == c) = False):
    pairUp [head, ..xs] ys = pairUp xs ys :=
  pairUp.eq2 head xs ys notArm1

theorem pairUpAtMost ∀ (xs ys: List Nat): pairUp xs ys ≤ xs.length := match induct (pairUp xs ys) with
  | eq1 head b xs c ys guard ih => arithmetic
  | eq2 head xs ys notArm1 ih =>
    let skip := pairUpSkip head xs ys notArm1
    arithmetic
  | eq3 _ => arithmetic

-- Applied to the next values, `notArm1` is the `= False` fact.
theorem pairUpNext ∀ (head b c: Nat) (xs1 ys1: List Nat)
    (notArm1: ∀ (b1: Nat) (xs2: List Nat) (c1: Nat) (ys2: List Nat) => [b, ..xs1] = [b1, ..xs2]
      → [c, ..ys1] = [c1, ..ys2]
      → (b1 == c1) = False):
    (b == c) = False :=
  notArm1 b xs1 c ys1 byComputing byComputing
