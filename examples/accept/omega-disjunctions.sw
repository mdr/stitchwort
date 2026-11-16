-- `arithmetic` with disjunctions, `Bool` logic and record fields: a fact
-- `Or p q` or `(p || q) = True` is split into its two cases when the facts
-- without it aren't enough; `||`, `&&` and `not` around comparisons, and
-- `==` on `Nat`s and `Int`s, are read as the propositions they decide; a
-- goal `Or p q` or `(p || q) = True` is proved by cases on one side.

import Std (And, Bool, Eq, Int, Nat, Not, Or, Void)

theorem orFact ∀ (a: Nat) (h: (a = 1) ∨ (a = 2)): a <= 2 := arithmetic

theorem boolOrFact ∀ (a: Nat) (h: (a == 1 || a == 2) = True): 1 <= a := arithmetic

theorem intOrFact ∀ (x: Int) (h: (x = -1) ∨ (x = 1)): x * 2 <= 2 := arithmetic

-- Nested: each case has a disjunction of its own.
theorem nested ∀ (a b: Nat)
    (h: ((a == 1 && (b == 2 || b == 3)) || (a == 2 && (b + 1 == 3 || b == 0))) = True):
    a + b <= 4 :=
  arithmetic

-- `False` sides: `(p || q) = False` is both false, `(p && q) = False` is a
-- disjunction.
theorem orFalseFact ∀ (a: Nat) (h: (a == 1 || a < 5) = False): 5 <= a := arithmetic

theorem andFalseFact ∀ (a: Nat) (k: a <= 3) (h: (1 <= a && a <= 2) = False): (a = 0) ∨ (a = 3) := arithmetic

theorem notOrFact ∀ (a: Nat) (h: (a == 1 || a == 2) ≠ True) (k: 1 <= a): 3 <= a := arithmetic

-- `==`, `!=` and `not`.
theorem eqFact ∀ (a b: Nat) (h: (a == b) = True): a <= b := arithmetic

theorem eqGoal ∀ (a b: Nat) (k: a <= b) (l: b <= a): (a == b) = True := arithmetic

theorem intEqFact ∀ (x y: Int) (h: (x == y) = True): x <= y := arithmetic

def differ (a b: Nat): Bool := a != b

theorem differFact ∀ (a b: Nat) (h: differ a b = True) (k: a <= b): a < b := arithmetic

theorem notGoal ∀ (a: Nat) (k: a < 3): Bool.not (a == 3) = True := arithmetic

theorem notFact ∀ (a: Nat) (k: a <= 3) (h: Bool.not (a == 3) = True): a < 3 := arithmetic

-- Goals.
theorem orGoal ∀ (a: Nat): (a <= 3 || 4 <= a) = True := arithmetic

theorem orPropGoal ∀ (a: Nat): (a <= 3) ∨ (4 <= a) := arithmetic

theorem orEqGoal ∀ (a: Nat) (h: a <= 1): (a = 0) ∨ (a = 1) := arithmetic

theorem orFalseGoal ∀ (a: Nat) (k: a < 3): (a == 3 || a == 4) = False := arithmetic

theorem andFalseGoal ∀ (a: Nat) (k: a < 3): (3 <= a && a <= 5) = False := arithmetic

-- A step on a grid, as a `Bool` and as a proposition: `arithmetic` goes between
-- them, splitting the step's disjunctions.
type Position = { row: Nat, column: Nat }

def isOrthogonalStep (from to: Position): Bool :=
  (from.row == to.row && (from.column + 1 == to.column || to.column + 1 == from.column))
    || (from.column == to.column && (from.row + 1 == to.row || to.row + 1 == from.row))

def Orthogonal (from to: Position): Prop :=
  ((from.row = to.row) ∧ ((from.column + 1 = to.column) ∨ (to.column + 1 = from.column)))
    ∨ ((from.column = to.column) ∧ ((from.row + 1 = to.row) ∨ (to.row + 1 = from.row)))

theorem orthogonalElim ∀ (from to: Position) (step: isOrthogonalStep from to = True): Orthogonal from to := arithmetic

theorem orthogonalIntro ∀ (from to: Position) (o: Orthogonal from to): isOrthogonalStep from to = True := arithmetic

theorem stepMoves ∀ (from: Position) (step: isOrthogonalStep from from = True): Void := arithmetic

-- A field of a record literal is computed: here the record is only known
-- once `arithmetic`'s goal has been unified with the expected type.
theorem rowsApart ∀ (first second: Position) (apart: first.row ≠ second.row): first ≠ second := same =>
  apart (Eq.cong (position => position.row) same)

theorem apart ∀ (up column: Nat): ({ row = up + 1, column }: Position) ≠ ({ row = up, column }) :=
  rowsApart _ _ (arithmetic)
