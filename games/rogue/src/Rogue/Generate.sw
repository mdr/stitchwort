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

-- The level at `depth`: every number it needs is drawn first (`drawMore`),
-- and then the level is planned from them with no randomness left
-- (`planFrom`). Its rooms are joined in a snake through the sections (top
-- row left to right, bottom row right to left), and sometimes by one more
-- corridor, so every room can be reached from every other (proved for
-- every seed: `generatedReachable`, Proofs/Generated.sw).
-- Opaque: no proof about a turn needs to look inside the generator, and
-- turns run it on an unknown seed (see `descend`).
opaque def generateLevel (depth: Nat): {Random} Plan := planFrom depth (drawMore [] (drawCount depth))

-- The numbers `drawn` so far, then `count` more from the generator, in
-- order. (Drawn onto the end, rather than as `Cons first (draws rest)`, so
-- that what the seeded handler makes of it is proved by induction:
-- `seededDrawMore`, Proofs/Generated.sw.)
def drawMore (drawn: List Nat): Nat → {Random} List Nat
  | 0 => drawn
  | Succ remaining =>
    let number := next()
    drawMore (drawn ++ [number]) remaining

-- Where in the draws each part of a level finds its numbers: four for each
-- of the six rooms, three for the entrance, the exit and the extra
-- corridor, four for each monster, and three for each item.
def roomDraws: Nat := 4

def layoutDraws: Nat := 6 * roomDraws + 3

def monsterDraws: Nat := 4

def itemDraws: Nat := 3

def monsterCount (depth: Nat): Nat := 2 + 2 * depth

def potionCount: Nat := 2

def swordCount (depth: Nat): Nat := if depth < deepest then 1 else 0

-- The first of the items' draws, and how many there are in all. The count is
-- opaque so that a proof about the generator with an unknown depth doesn't
-- start drawing (Proofs/Generated.sw).
def itemsFrom (depth: Nat): Nat := layoutDraws + monsterDraws * monsterCount depth

opaque def drawCount (depth: Nat): Nat := itemsFrom depth + itemDraws * (potionCount + swordCount depth)

-- Draw number `index` as a roll from 0 up to `most`, as `roll most` makes
-- it from the generator's number.
def rollAt (numbers: List Nat) (index: Nat) (most: Nat): Nat := numbers.getOr 0 index % Succ most

-- The level at `depth` planned from the drawn `numbers`.
def planFrom (depth: Nat) (numbers: List Nat): Plan :=
  let rooms := roomsFrom numbers
  let entranceIndex := entranceFrom numbers
  let level := layOut depth rooms entranceIndex (exitFrom numbers) (extraFrom numbers)
  let monsters := (List.range (monsterCount depth)).map (index => monsterFrom depth numbers rooms entranceIndex (layoutDraws + monsterDraws * index))
  let potions := (List.range potionCount).map (index => itemFrom Potion numbers rooms (itemsFrom depth + itemDraws * index))
  let swords := if depth < deepest then [itemFrom Sword numbers rooms (itemsFrom depth + itemDraws * potionCount)] else []
  let amulets := if depth < deepest then [] else [({ loot = Amulet, position = level.goal }: Item)]
  { level, monsters, items = amulets ++ swords ++ potions }

-- The six rooms, one in each section.
def roomsFrom (numbers: List Nat): List Area := (List.range 6).map (roomFrom numbers)

-- The number of the room the player arrives in: 0 to 5.
def entranceFrom (numbers: List Nat): Nat := rollAt numbers (6 * roomDraws) 5

-- The number of the room with the way on: one of the other five.
def exitFrom (numbers: List Nat): Nat := (entranceFrom numbers + 1 + rollAt numbers (6 * roomDraws + 1) 4) % 6

-- Which extra corridor there is, if any (see `roomLinks`).
def extraFrom (numbers: List Nat): Nat := rollAt numbers (6 * roomDraws + 2) 2

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
-- Its four draws from `roomDraws * index`: its height, width, row and column.
def roomFrom (numbers: List Nat) (index: Nat): Area :=
  let first := roomDraws * index
  let top := (index / 3) * sectionRows + 1
  let left := (index % 3) * sectionColumns + 1
  let down := 2 + rollAt numbers first 3
  let across := 4 + rollAt numbers (first + 1) 10
  let row := top + rollAt numbers (first + 2) (sectionRows - 3 - down)
  let column := left + rollAt numbers (first + 3) (sectionColumns - 3 - across)
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

-- A cell somewhere in an area, from draws `first` and `first + 1`.
def spotFrom (numbers: List Nat) (first: Nat) (area: Area): Position :=
  { row = area.corner.row + rollAt numbers first area.down, column = area.corner.column + rollAt numbers (first + 1) area.across }

-- Deeper levels have fewer goblins and more orcs and trolls.
def kindFor (depth: Nat) (chance: Nat): Kind :=
  match depth with
    | 0 => Goblin
    | 1 => if chance < 8 then Goblin else Orc
    | 2 => if chance < 4 then Goblin else if chance < 9 then Orc else Troll
    | _ => if chance < 2 then Goblin else if chance < 6 then Orc else Troll

-- A monster in a room other than the entrance, from the four draws from
-- `first`: its room, its kind, and its row and column.
def monsterFrom (depth: Nat) (numbers: List Nat) (rooms: List Area) (entranceIndex: Nat) (first: Nat): Monster :=
  let room := roomOf rooms ((entranceIndex + 1 + rollAt numbers first 4) % 6)
  let kind := kindFor depth (rollAt numbers (first + 1) 9)
  { kind, position = spotFrom numbers (first + 2) room, hitPoints = kind.startingHitPoints }

-- An item in any room, from the three draws from `first`: its room, and its
-- row and column.
def itemFrom (loot: Loot) (numbers: List Nat) (rooms: List Area) (first: Nat): Item :=
  { loot, position = spotFrom numbers (first + 1) (roomOf rooms (rollAt numbers first 5)) }

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
