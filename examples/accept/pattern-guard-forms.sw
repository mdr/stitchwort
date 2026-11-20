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
