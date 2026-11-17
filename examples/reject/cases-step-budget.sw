-- expect-error: E-CASES-BUDGET
-- The goal holds a whole drawn map, 20 rows of 66 cells, every cell a test
-- stuck on the map's fields. Each case `cases` makes costs millions of
-- evaluation steps to search and split, so its 64-case budget alone would
-- let this run for many minutes; its step budget stops it first (SW-3846).
import Std (List)

type Spot = { row: Nat, column: Nat }

type Area = { corner: Spot, down: Nat, across: Nat }

def Area.contains (area: Area) (spot: Spot): Bool :=
  area.corner.row ≤ spot.row ≤ area.corner.row + area.down
    ∧ area.corner.column ≤ spot.column ≤ area.corner.column + area.across

type Map = { depth: Nat, entrance: Area, exit: Area, rooms: List Area }

def cellAt (map: Map) (spot: Spot): Char :=
  if map.depth < 3 ∧ map.exit.contains spot then '>'
  else if map.entrance.contains spot ∨ map.rooms.any (.contains spot) then '.'
  else ' '

def draw (map: Map): List (List Char) :=
  List.range 0 20 |> .map (row => List.range 0 66 |> .map (column => cellAt map { row, column }))

theorem rowWidth ∀ (map: Map) (row: Nat) (small: row < 20): ((draw map).getOr row []).length = 66 := cases
