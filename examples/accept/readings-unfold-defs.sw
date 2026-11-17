-- A fact whose test is a plain `Bool` definition is taken apart by what the
-- definition unfolds to, whatever the goal is: a `let` pattern with a goal
-- that is a membership or a `∃` reads it the same as a `match` or a goal
-- that is an equation (SW-3096).
import Std (Bool, Eq, Exists, List, Nat, Option)

type Spot = { row: Nat, column: Nat }

type Field = { height: Nat, width: Nat }

def Spot.within (spot: Spot) (field: Field): Bool := spot.row < field.height && spot.column < field.width

def Field.contains (field: Field) (spot: Spot): Bool := spot.within field

def sameRow (a b: Spot): Bool := a.row == b.row

def besideEachOther (a b: Spot): Bool := sameRow a b && (a.column + 1 == b.column || b.column + 1 == a.column)

def stacked (a b: Spot): Bool := sameRow a b && (a.row < b.row && b.row < a.row + 5)

-- the goal is an equation
theorem equationGoal ∀ (a b: Spot) (h: besideEachOther a b): sameRow a b = True :=
  let Both same _ := h
  same

-- the goal is a membership
theorem membershipGoal ∀ (a b: Spot) (spots: List Spot) (h: besideEachOther a b)
    (m: sameRow a b = True → b ∈ spots):
    b ∈ spots :=
  let Both same _ := h
  m same

theorem membershipFromPart ∀ (a b: Spot) (spots: List Spot)
    (h: (a ∈ spots) ∧ besideEachOther a b)
    (m: sameRow a b = True → a ∈ spots):
    a ∈ spots :=
  let Both _ (Both same _) := h
  m same

-- the goal is an existential
theorem existsGoal ∀ (a b: Spot) (h: besideEachOther a b): Exists Nat (n => n = a.row ∧ sameRow a b = True) :=
  let Both same _ := h
  Witness a.row (Both byComputing same)

-- a method of a record, through another method
theorem methodGoal ∀ (field: Field) (spot: Spot) (spots: List Spot) (h: field.contains spot)
    (m: spot.row < field.height → spot ∈ spots):
    spot ∈ spots :=
  let Both rowIn _ := h
  m rowIn

theorem methodPartBuilt ∀ (field: Field) (spot: Spot)
    (rowIn: spot.row < field.height)
    (columnIn: spot.column < field.width):
    field.contains spot = True :=
  Both rowIn columnIn

-- a nested reading: the inner parts of a `let` pattern are used
def nestedGoal (a b: Spot) (h: stacked a b) (m: a.row < b.row → b.row < a.row + 5 → Nat): Nat :=
  let Both _ (Both less below) := h
  m less below

-- a lambda's parameter can be taken apart too, in a `def` whose goal isn't a
-- proposition
def lambdaGoal (a b: Spot) (m: sameRow a b = True → Nat): besideEachOther a b → Nat := (Both same _) => m same

-- and in a theorem, with a membership goal
theorem lambdaTheorem ∀ (a b: Spot) (spots: List Spot) (h: besideEachOther a b)
    (m: sameRow a b = True → b ∈ spots):
    b ∈ spots :=
  let f: besideEachOther a b → b ∈ spots := (Both same _) => m same
  f h

-- `= False` reads as a conjunction of `= False` facts; its parts are used
def falseGoal (a b: Nat) (h: (a == 0 || b == 0) = False) (m: (a == 0) = False → (b == 0) = False → Nat): Nat :=
  let Both na nb := h
  m na nb
