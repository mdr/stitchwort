-- `omega` with disjunctions, `Bool` logic and record fields: a fact
-- `Or p q` or `(p || q) = True` is split into its two cases when the facts
-- without it aren't enough; `||`, `&&` and `not` around comparisons, and
-- `==` on `Nat`s and `Int`s, are read as the propositions they decide; a
-- goal `Or p q` or `(p || q) = True` is proved by cases on one side.

import Std (And, Bool, Eq, Int, Nat, Not, Or, Void)

theorem orFact (a: Nat) (h: Or (a = 1) (a = 2)): a <= 2 := omega

theorem boolOrFact (a: Nat) (h: (a == 1 || a == 2) = True): 1 <= a := omega

theorem intOrFact (x: Int) (h: Or (x = -1) (x = 1)): x * 2 <= 2 := omega

-- Nested: each case has a disjunction of its own.
theorem nested (a: Nat) (b: Nat) (h: ((a == 1 && (b == 2 || b == 3)) || (a == 2 && (b + 1 == 3 || b == 0))) = True):
    a + b <= 4 := omega

-- `False` sides: `(p || q) = False` is both false, `(p && q) = False` is a
-- disjunction.
theorem orFalseFact (a: Nat) (h: (a == 1 || a < 5) = False): 5 <= a := omega

theorem andFalseFact (a: Nat) (k: a <= 3) (h: (1 <= a && a <= 2) = False): Or (a = 0) (a = 3) := omega

theorem notOrFact (a: Nat) (h: Not ((a == 1 || a == 2) = True)) (k: 1 <= a): 3 <= a := omega

-- `==`, `!=` and `not`.
theorem eqFact (a: Nat) (b: Nat) (h: (a == b) = True): a <= b := omega

theorem eqGoal (a: Nat) (b: Nat) (k: a <= b) (l: b <= a): (a == b) = True := omega

theorem intEqFact (x: Int) (y: Int) (h: (x == y) = True): x <= y := omega

def differ (a: Nat) (b: Nat): Bool := a != b

theorem differFact (a: Nat) (b: Nat) (h: differ a b = True) (k: a <= b): a < b := omega

theorem notGoal (a: Nat) (k: a < 3): Bool.not (a == 3) = True := omega

theorem notFact (a: Nat) (k: a <= 3) (h: Bool.not (a == 3) = True): a < 3 := omega

-- Goals.
theorem orGoal (a: Nat): (a <= 3 || 4 <= a) = True := omega

theorem orPropGoal (a: Nat): Or (a <= 3) (4 <= a) := omega

theorem orEqGoal (a: Nat) (h: a <= 1): Or (a = 0) (a = 1) := omega

theorem orFalseGoal (a: Nat) (k: a < 3): (a == 3 || a == 4) = False := omega

theorem andFalseGoal (a: Nat) (k: a < 3): (3 <= a && a <= 5) = False := omega

-- A step on a grid, as a `Bool` and as a proposition: `omega` goes between
-- them, splitting the step's disjunctions.
type Position = { row: Nat, column: Nat }

def isOrthogonalStep (from: Position) (to: Position): Bool :=
  (from.row == to.row && (from.column + 1 == to.column || to.column + 1 == from.column))
    || (from.column == to.column && (from.row + 1 == to.row || to.row + 1 == from.row))

def Orthogonal (from: Position) (to: Position): Prop :=
  Or (And (from.row = to.row) (Or (from.column + 1 = to.column) (to.column + 1 = from.column)))
    (And (from.column = to.column) (Or (from.row + 1 = to.row) (to.row + 1 = from.row)))

theorem orthogonalElim (from: Position) (to: Position) (step: isOrthogonalStep from to = True): Orthogonal from to := omega

theorem orthogonalIntro (from: Position) (to: Position) (o: Orthogonal from to): isOrthogonalStep from to = True := omega

theorem stepMoves (from: Position) (step: isOrthogonalStep from from = True): Void := omega

-- A field of a record literal is computed: here the record is only known
-- once `omega`'s goal has been unified with the expected type.
theorem rowsApart (first: Position) (second: Position) (apart: Not (first.row = second.row)): Not (first = second) :=
  same => apart (Eq.cong (position => position.row) same)

theorem apart (up: Nat) (column: Nat): Not (({ row = up + 1, column }: Position) = { row = up, column }) := rowsApart _ _ (omega)
