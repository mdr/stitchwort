-- Making levels. The generator draws rooms, corridors, monsters and items
-- with the `Random` ability, and `arrive` puts the player on the new level
-- and places its monsters and items, keeping only those on floor, off the
-- player's start, and one to a cell (proved in Proofs/Level.sw).

namespace Rogue
import Std (List, Nat, Text)

-- A level is two rows of three sections, with a room in each, and rock
-- between them.
def sectionRows: Nat := 10

def sectionColumns: Nat := 22

-- What the generator makes: a level, and where it would like its monsters
-- and items to go.
type Plan = { level: Level, monsters: List Monster, items: List Item }

-- The level at `depth`. Its rooms are joined in a snake through the
-- sections (top row left to right, bottom row right to left), and sometimes
-- by one more corridor, so every room can be reached from every other.
def generateLevel (depth: Nat): {Random} Plan :=
  let rooms := (List.range 6).map randomRoom
  let room := (index: Nat) => rooms.getOr (rooms.headOr fallbackRoom) index
  let entranceIndex := roll 5
  let exitIndex := (entranceIndex + 1 + roll 4) % 6
  let corridors := (roomLinks (roll 2)).flatMap (((first, second)) => corridorBetween (room first).middle (room second).middle)
  let level := Level.build depth (room entranceIndex) (room exitIndex) rooms corridors
  let monsters := (List.range (2 + 2 * depth)).map (_ => randomMonster depth (room ((entranceIndex + 1 + roll 4) % 6)))
  let potions := (List.range 2).map (_ => randomItem Potion (room (roll 5)))
  let swords := if depth < deepest then [randomItem Sword (room (roll 5))] else []
  let amulets := if depth < deepest then [] else [({ loot = Amulet, position = level.goal }: Item)]
  { level, monsters, items = amulets ++ swords ++ potions }

-- Never used: `rooms` always has six.
def fallbackRoom: Area := { corner = { row = 1, column = 1 }, down = 0, across = 0 }

-- A room somewhere in section `index` (0 to 5, left to right and then top
-- to bottom), leaving rock all round it: 3 to 6 rows by 5 to 15 columns.
def randomRoom (index: Nat): {Random} Area :=
  let top := (index / 3) * sectionRows + 1
  let left := (index % 3) * sectionColumns + 1
  let down := 2 + roll 3
  let across := 4 + roll 10
  let row := top + roll (sectionRows - 3 - down)
  let column := left + roll (sectionColumns - 3 - across)
  { corner = { row, column }, down, across }

-- The pairs of rooms joined by corridors: the snake, and one more.
def roomLinks (extra: Nat): List (Nat, Nat) :=
  let more :=
    match extra with
      | 0 => [(0, 3)]
      | 1 => [(1, 4)]
      | _ => []
  [(0, 1), (1, 2), (2, 5), (5, 4), (4, 3)] ++ more

-- A corridor from one cell to another: along the first's row, then along
-- the second's column.
def corridorBetween (origin: Position) (target: Position): List Area := [
  { corner = { row = origin.row, column = Nat.min origin.column target.column }, down = 0, across = distanceBetween origin.column target.column },
  { corner = { row = Nat.min origin.row target.row, column = target.column }, down = distanceBetween origin.row target.row, across = 0 }
]

-- A cell somewhere in an area.
def randomSpot (area: Area): {Random} Position :=
  { row = area.corner.row + roll area.down, column = area.corner.column + roll area.across }

-- Deeper levels have fewer goblins and more orcs and trolls.
def kindFor (depth: Nat) (chance: Nat): Kind :=
  match depth with
    | 0 => Goblin
    | 1 => if chance < 8 then Goblin else Orc
    | 2 => if chance < 4 then Goblin else if chance < 9 then Orc else Troll
    | _ => if chance < 2 then Goblin else if chance < 6 then Orc else Troll

def randomMonster (depth: Nat) (room: Area): {Random} Monster :=
  let kind := kindFor depth (roll 9)
  { kind, position = randomSpot room, hitPoints = kind.startingHitPoints }

def randomItem (loot: Loot) (room: Area): {Random} Item := { loot, position = randomSpot room }

-- The player arrives at the start of a planned level, with the planned
-- monsters and items that may stand where they were planned.
def arrive (state: State) (plan: Plan): State :=
  let start := plan.level.start
  {
    state |
    level = plan.level,
    player = start,
    monsters = placeMonsters plan.level start [] plan.monsters,
    items = placeItems plan.level start [] plan.items
  }

-- The monsters placed so far, and then each that `pickFree` lets stand
-- where it was planned: not in a wall, on the start, or on another monster.
def placeMonsters (level: Level) (start: Position) (placed: List Monster): List Monster → List Monster
  | [] => placed
  | Cons monster rest =>
    match pickFree level [monster.position] start placed with
      | Some position => placeMonsters level start (placed ++ [{ monster | position }]) rest
      | None => placeMonsters level start placed rest

-- The items placed so far, and then each that isn't in a wall, on the
-- start, on the stairs, or on another item.
def placeItems (level: Level) (start: Position) (placed: List Item): List Item → List Item
  | [] => placed
  | Cons item rest =>
    if isWall level item.position ∨ item.position == start ∨ isStairs level item.position ∨ (itemAt item.position placed).isSome then placeItems level start placed rest
    else placeItems level start (placed ++ [item]) rest

-- A new game, on the first level. Every level is made now, at the edge,
-- rather than when the player goes down: `resolve` is pure, and the
-- generator run inside it by a handler of its own made the checker unfold
-- the generator in every proof about a turn (NOTES.md, stage 2).
def newGame(): {Random} State :=
  let first := generateLevel 1
  let deeper := (List.between 2 deepest).map generateLevel
  startingState first deeper

def startingState (plan: Plan) (deeper: List Plan): State := arrive (freshState plan deeper) plan

-- The player before arriving on the first level.
def freshState (plan: Plan) (deeper: List Plan): State := {
  level = plan.level,
  below = deeper,
  player = plan.level.start,
  hitPoints = maxHitPoints,
  potions = 0,
  strength = startingStrength,
  monsters = [],
  items = [],
  turn = 0,
  message = "Find the amulet, ${deepest} levels down.",
  phase = Playing
}
