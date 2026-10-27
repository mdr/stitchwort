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
-- by one more corridor, so every room can be reached from every other
-- (proved for any rooms: `goalReachable`, Proofs/Reach.sw).
-- Opaque: no proof about a turn needs to look inside the generator, and
-- turns run it on an unknown seed (see `descend`).
opaque def generateLevel (depth: Nat): {Random} Plan :=
  let rooms := List.range 6 |> .map roomFrom
  let entranceIndex := roll 5
  let awayFromEntrance := () => (entranceIndex + 1 + roll 4) % 6
  let exitIndex := awayFromEntrance ()
  let extra := roll 2
  let level := layOut depth rooms entranceIndex exitIndex extra
  let monsters := List.range (monsterCount depth) |> .map (_ => monsterFrom depth (roomOf rooms (awayFromEntrance ())))
  let potions := List.range potionCount |> .map (_ => itemFrom Potion rooms)
  let swords := if depth < deepest then [itemFrom Sword rooms] else []
  let amulets := if depth < deepest then [] else [({ loot = Amulet, position = level.goal }: Item)]
  { level, monsters, items = amulets ++ swords ++ potions }

def monsterCount (depth: Nat): Nat := 2 + 2 * depth

def potionCount: Nat := 2

-- The level's rooms joined by its corridors, with no rolls left to make:
-- the stairs can be reached from the start of every level it makes
-- (Proofs/Reach.sw). Opaque: with unknown rooms, its terrain would be
-- drawn out cell by cell wherever a proof compared two levels.
opaque def layOut (depth: Nat) (rooms: List Area) (entranceIndex: Nat) (exitIndex: Nat) (extra: Nat): Level :=
  Level.build depth (roomOf rooms entranceIndex) (roomOf rooms exitIndex) rooms (corridorsOf rooms extra)

-- The corridors joining the rooms `roomLinks` pairs up, middle to middle.
def corridorsOf (rooms: List Area) (extra: Nat): List Area :=
  (roomLinks extra).flatMap (((first, second)) => corridorBetween (roomOf rooms first).middle (roomOf rooms second).middle)

-- Room number `index`.
def roomOf (rooms: List Area) (index: Nat): Area := rooms.getOr (rooms.headOr fallbackRoom) index

-- Never used: `rooms` always has six.
def fallbackRoom: Area := { corner = { row = 1, column = 1 }, down = 0, across = 0 }

-- A room somewhere in section `index` (0 to 5, left to right and then top
-- to bottom), leaving rock all round it: 3 to 6 rows by 5 to 15 columns.
-- (It fits inside its section whatever the rolls: `roomFits`,
-- Proofs/Bounds.sw.)
def roomFrom (index: Nat): {Random} Area :=
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
def spotIn (area: Area): {Random} Position :=
  { row = area.corner.row + roll area.down, column = area.corner.column + roll area.across }

-- Deeper levels have fewer goblins and more orcs and trolls.
def kindFor (depth: Nat) (chance: Nat): Kind :=
  match depth with
    | 0 => Goblin
    | 1 => if chance < 8 then Goblin else Orc
    | 2 => if chance < 4 then Goblin else if chance < 9 then Orc else Troll
    | _ => if chance < 2 then Goblin else if chance < 6 then Orc else Troll

-- A monster somewhere in `room`.
def monsterFrom (depth: Nat) (room: Area): {Random} Monster :=
  let kind := kindFor depth (roll 9)
  { kind, position = spotIn room, hitPoints = kind.startingHitPoints }

-- An item somewhere in any room.
def itemFrom (loot: Loot) (rooms: List Area): {Random} Item := { loot, position = spotIn (roomOf rooms (roll 5)) }

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

-- A new game, on the first level. Deeper levels are made on the stairs.
def newGame(): {Random} State := startingState (generateLevel 1)

def startingState (plan: Plan): State := arrive (freshState plan) plan

-- The player before arriving on the first level.
def freshState (plan: Plan): State := {
  level = plan.level,
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
