-- A `match h: …` hypothesis is shown as written, `isWall p = False`, not
-- unfolded into the map `isWall` reads (games/rogue/NOTES.md item 14).
import Std (List)

def map: List (List Char) := [['#', '#', '#'], ['#', '.', '#'], ['#', '#', '#']]

def isWall (row: Nat) (column: Nat): Bool := (map.getOr [] row).getOr '#' column == '#'

theorem stepped (row: Nat) (column: Nat): row = row :=
  match wall: isWall row column with
    | True => rfl
    | False => ?
