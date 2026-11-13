-- A fact whose test is a plain `Bool` definition is taken apart by what the
-- definition unfolds to, whatever the goal is: a `let` pattern with a goal
-- that is a membership or a `∃` reads it the same as a `match` or a goal
-- that is an equation (SW-3096).
import Std (Bool, Eq, Exists, List, Nat, Option)

type Spot = { row: Nat, column: Nat }

type Field = { height: Nat, width: Nat }

def Spot.within (spot: Spot) (field: Field): Bool := spot.row < field.height && spot.column < field.width

def Field.contains (field: Field) (spot: Spot): Bool := spot.within field

def sameRow (a: Spot) (b: Spot): Bool := a.row == b.row

def besideEachOther (a: Spot) (b: Spot): Bool := sameRow a b && (a.column + 1 == b.column || b.column + 1 == a.column)

-- the goal is an equation
theorem equationGoal (a: Spot) (b: Spot) (h: besideEachOther a b): sameRow a b = True :=
  let Both same _ := h
  same

-- the goal is a membership
theorem membershipGoal (a: Spot) (b: Spot) (spots: List Spot) (h: besideEachOther a b) (member: b ∈ spots): b ∈ spots :=
  let Both same _ := h
  member

theorem membershipFromPart (a: Spot) (b: Spot) (spots: List Spot) (h: (a ∈ spots) ∧ besideEachOther a b): a ∈ spots :=
  let Both here (Both same _) := h
  here

-- the goal is an existential
theorem existsGoal (a: Spot) (b: Spot) (h: besideEachOther a b): Exists Nat (n => n = a.row) :=
  let Both same _ := h
  Witness a.row rfl

-- a method of a record, through another method
theorem methodGoal (field: Field) (spot: Spot) (spots: List Spot) (h: field.contains spot) (member: spot ∈ spots): spot ∈ spots :=
  let Both rowIn _ := h
  member

theorem methodPartBuilt (field: Field) (spot: Spot) (rowIn: spot.row < field.height) (columnIn: spot.column < field.width): field.contains spot = True :=
  Both rowIn columnIn
