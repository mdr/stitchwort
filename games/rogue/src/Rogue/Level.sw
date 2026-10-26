-- A level of the dungeon: rooms joined by corridors, each a rectangle of
-- floor (an `Area`). Everything else is rock; the rock round a room is drawn
-- as its walls (`#`).

namespace Rogue
import Std (List, Text)

-- The size of every level, in cells.
def levelRows: Nat := 20

def levelColumns: Nat := 66

-- How many levels down the amulet lies.
def deepest: Nat := 3

-- A rectangle of floor: the cells from `corner` to `down` rows further down
-- and `across` columns further right. It's never empty: `corner` is in it.
type Area = { corner: Position, down: Nat, across: Nat }

def Area.contains (area: Area) (position: Position): Bool :=
  area.corner.row ≤ position.row ∧ position.row ≤ area.corner.row + area.down ∧ area.corner.column ≤ position.column ∧ position.column ≤ area.corner.column + area.across

-- The middle cell (or the one just above or left of the middle).
def Area.middle (area: Area): Position := { row = area.corner.row + area.down / 2, column = area.corner.column + area.across / 2 }

-- The area and a border one cell wide: where a room's walls are drawn.
def Area.withWalls (area: Area): Area :=
  { corner = { row = area.corner.row - 1, column = area.corner.column - 1 }, down = area.down + 2, across = area.across + 2 }

-- One level: the player arrives in the middle of the `entrance`, and the
-- way on (the stairs, or the amulet on the deepest level) is in the middle
-- of the `exit`. `rooms` are all the rooms, the entrance and exit included.
-- `terrain` is the level drawn without its occupants, made once by
-- `Level.build` so that a frame doesn't redraw the rock.
type Level = {
  depth: Nat,
  entrance: Area,
  exit: Area,
  rooms: List Area,
  corridors: List Area,
  terrain: List (List Char)
}

def Level.start (level: Level): Position := level.entrance.middle

def Level.goal (level: Level): Position := level.exit.middle

-- The entrance comes first, so the start is floor on every level, however
-- the level was made (Proofs/Level.sw).
def isFloor (level: Level) (position: Position): Bool :=
  level.entrance.contains position ∨ level.exit.contains position ∨ level.rooms.any (.contains position) ∨ level.corridors.any (.contains position)

def isWall (level: Level) (position: Position): Bool := ¬isFloor level position

-- Every level but the deepest has stairs down, at its goal.
def isStairs (level: Level) (position: Position): Bool := level.depth < deepest ∧ position == level.goal

def Level.build (depth: Nat) (entrance: Area) (exit: Area) (rooms: List Area) (corridors: List Area): Level :=
  let undrawn: Level := { depth, entrance, exit, rooms, corridors, terrain = [] }
  { undrawn | terrain = drawTerrain undrawn }

def drawTerrain (level: Level): List (List Char) :=
  List.range levelRows |> .map (row => List.range levelColumns |> .map (column => terrainAt level { row, column }))

def terrainAt (level: Level) (position: Position): Char :=
  if isStairs level position then '>'
  else if isFloor level position then '.'
  else if level.rooms.any (room => room.withWalls.contains position) then '#'
  else ' '
