-- Derived `Ord` for records (docs/proposals/interfaces.md §5.11, §7.3):
-- lexicographic, field by field in the order they're declared. Proof
-- fields are left out of the comparison (D179).

import Std (List, Ord)

type Item = { name: Text, price: Nat }

def tea: Item := { name = "tea", price = 3 }
def jam: Item := { name = "jam", price = 4 }
def cheapJam: Item := { name = "jam", price = 2 }

test "by name first" := Ord.compare jam tea == Less
test "then by price" := Ord.compare jam cheapJam == Greater
test "equal" := Ord.compare tea { name = "tea", price = 3 } == Equal

-- Sorting a list of records with the generic `List.sort`.
def items: List Item := [tea, jam, cheapJam]

test "sort" := List.sort items == [cheapJam, jam, tea]
test "minimum" := List.minimum items == Some cheapJam

-- The introduction's `Dial`: a value parameter, and a proof field, which is
-- left out. Dials are ordered by `position`.
type Dial (highest: Nat) = { position: Nat, inRange: position ≤ highest }

def dial3: Dial 10 := { position = 3, inRange = rfl }
def dial7: Dial 10 := { position = 7, inRange = rfl }

test "dials by position" := Ord.compare dial3 dial7 == Less
test "dials sorted" := List.sort [dial7, dial3] == [dial3, dial7]
test "dial max" := Ord.max dial3 dial7 == dial7

-- A record with no data fields has one value.
type None2 = { same: 1 = 1 }

test "no data" := Ord.compare ({ same = rfl }: None2) { same = rfl } == Equal

-- A record whose fields are lists and pairs.
type Score = { names: List Text, best: (Nat, Text) }

test "nested" := Ord.compare ({ names = ["a"], best = (1, "x") }: Score) { names = ["a"], best = (1, "y") } == Less

-- The laws hold for every record, not just these.
theorem itemTrans (x: Item) (y: Item) (z: Item) (h1: Ord.compare x y = Less) (h2: Ord.compare y z = Less):
    Ord.compare x z = Less :=
  Ord.trans x y z h1 h2
