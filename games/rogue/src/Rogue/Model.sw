-- The game's model: positions, monsters, items, commands and the state of a
-- game.

namespace Rogue

-- A cell of a level, counted from the top-left corner.
type Position = { row: Nat, column: Nat }

type Direction =
  | North
  | South
  | West
  | East

-- The neighbouring cell in a direction. Rows and columns stop at 0, but
-- every level has rock all round, so nothing ever walks off its top or left.
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
  | Troll

def Kind.glyph: Kind → Char
  | Goblin => 'g'
  | Orc => 'o'
  | Troll => 'T'

def Kind.name: Kind → Text
  | Goblin => "goblin"
  | Orc => "orc"
  | Troll => "troll"

def Kind.startingHitPoints: Kind → Nat
  | Goblin => 3
  | Orc => 7
  | Troll => 12

-- The most damage one blow does; a blow does 1 up to this.
def Kind.strength: Kind → Nat
  | Goblin => 2
  | Orc => 3
  | Troll => 4

type Monster = { kind: Kind, position: Position, hitPoints: Nat }

-- What lies on the floor: a potion (carried, and drunk with `p`), a sword
-- (wielded at once, so blows hit harder), or the amulet at the bottom of the
-- dungeon, which wins the game.
type Loot =
  | Potion
  | Sword
  | Amulet

def Loot.glyph: Loot → Char
  | Potion => '!'
  | Sword => ')'
  | Amulet => '"'

type Item = { loot: Loot, position: Position }

type Command =
  | Move (direction: Direction)
  | Wait
  | Descend
  | Drink
  | Quit

type Phase =
  | Playing
  | Won
  | Died
  | GaveUp

type State = {
  level: Level,
  player: Position,
  hitPoints: Nat,
  potions: Nat,
  strength: Nat,
  monsters: List Monster,
  items: List Item,
  turn: Nat,
  message: Text,
  phase: Phase
}

def maxHitPoints: Nat := 12

-- The player's strength before finding a sword: the most damage a blow
-- does. A blow does 2 up to the player's strength.
def startingStrength: Nat := 4

-- How much each sword adds to the player's strength.
def swordBonus: Nat := 2

-- How much a potion heals.
def potionStrength: Nat := 5

-- How close the player must be before a monster gives chase.
def sightRange: Nat := 7

-- The first monster standing on a cell, if any.
def monsterAt (position: Position): List Monster → Option Monster
  | [] => None
  | Cons monster others => if monster.position == position then Some monster else monsterAt position others

-- The first item lying on a cell, if any.
def itemAt (position: Position) (items: List Item): Option Item := items.find (item => item.position == position)
