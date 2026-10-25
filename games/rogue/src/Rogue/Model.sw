-- The game's model: positions, monsters, commands and the state of a game.

namespace Rogue

-- A cell of the dungeon, counted from the top-left corner.
type Position = { row: Nat, column: Nat }

type Direction =
  | North
  | South
  | West
  | East

-- The neighbouring cell in a direction. Rows and columns stop at 0, but the
-- dungeon has a wall all round, so nothing ever walks off its top or left.
def Position.toward (position: Position) (direction: Direction): Position :=
  match direction with
    | North => { position | row = position.row - 1 }
    | South => { position | row = position.row + 1 }
    | West => { position | column = position.column - 1 }
    | East => { position | column = position.column + 1 }

def distanceBetween (low: Nat) (high: Nat): Nat := (low - high) + (high - low)

-- Steps between two cells, moving only up, down, left and right.
def Position.distance (position: Position) (other: Position): Nat :=
  distanceBetween position.row other.row + distanceBetween position.column other.column

def Position.isNextTo (position: Position) (other: Position): Bool := position.distance other == 1

type Kind =
  | Goblin
  | Orc

def Kind.glyph: Kind → Char
  | Goblin => 'g'
  | Orc => 'o'

def Kind.name: Kind → Text
  | Goblin => "goblin"
  | Orc => "orc"

def Kind.startingHitPoints: Kind → Nat
  | Goblin => 3
  | Orc => 7

-- The most damage one blow does; a blow does 1 up to this.
def Kind.strength: Kind → Nat
  | Goblin => 2
  | Orc => 3

type Monster = { kind: Kind, position: Position, hitPoints: Nat }

type Command =
  | Move (direction: Direction)
  | Wait
  | Quit

type Phase =
  | Playing
  | Escaped
  | Died
  | GaveUp

type State = {
  player: Position,
  hitPoints: Nat,
  monsters: List Monster,
  potions: List Position,
  turn: Nat,
  message: Text,
  phase: Phase
}

def maxHitPoints: Nat := 12

-- The most damage the player's blow does; a blow does 2 up to this.
def playerStrength: Nat := 4

-- How much a potion heals.
def potionStrength: Nat := 5

-- How close the player must be before a monster gives chase.
def sightRange: Nat := 7

-- The first monster standing on a cell, if any.
def monsterAt (position: Position): List Monster → Option Monster
  | [] => None
  | Cons monster others => if monster.position == position then Some monster else monsterAt position others
