-- The dungeon: one hand-drawn level. `#` is wall, `+` an open door, `>` the
-- stairs down (the way out), `@` where the player starts, `g` and `o` a
-- goblin and an orc, and `!` a healing potion. Everything but `#` is floor.

namespace Rogue
import Std (List, Text)

def dungeonText: Text := """
  ############################################
  #........#..............#.......#..........#
  #..@.....#....g.........#.......+....o.....#
  #........+..............#.......#..........#
  #........#..............###+#####..........#
  #####+####......!.......#..................#
  #........#..............#.......######+#####
  #..g.....#######+########.......#..........#
  #........#..............#...g...#......>...#
  #....!...+..............+.......#..........#
  ############################################
  """

def dungeonRows: List (List Char) := dungeonText.lines.map (.toList)

-- The character drawn at a cell; past the edges, wall.
def charAt (position: Position): Char := (dungeonRows.getOr [] position.row).getOr '#' position.column

def isWall (position: Position): Bool := charAt position == '#'

def isStairs (position: Position): Bool := charAt position == '>'

-- What the floor looks like under a cell's starting occupant.
def terrainOf (char: Char): Char := if char == '#' ∨ char == '+' ∨ char == '>' then char else '.'

-- Every cell, with the character drawn there.
def cells: List (Position, Char) :=
  dungeonRows.withIndex.flatMap (((row, chars)) =>
    chars.withIndex.map (((column, char)) => (({ row, column }: Position), char)))

def cellsMarked (mark: Char): List Position := cells.filterMap (((position, char)) => if char == mark then Some position else None)

def monstersMarked (kind: Kind): List Monster :=
  (cellsMarked kind.glyph).map (position => ({ kind, position, hitPoints = kind.startingHitPoints }: Monster))

def initialState: State := {
  player = (cellsMarked '@').headOr { row = 1, column = 1 },
  hitPoints = maxHitPoints,
  monsters = monstersMarked Goblin ++ monstersMarked Orc,
  potions = cellsMarked '!',
  turn = 0,
  message = "Find the stairs (>) and escape.",
  phase = Playing
}
