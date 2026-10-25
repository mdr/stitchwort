-- The level generator, over many seeds: every level can be played (its goal
-- can be reached from its start), fits the screen, and gets harder further
-- down; and `arrive` keeps only the monsters and items that may stand where
-- they were planned.

namespace Rogue.Tests
import Rogue (..)
import Std (List, Set)

-- The seeds the generator is tried on.
def seeds: List Nat := List.range 40

def planned (seed: Nat) (depth: Nat): Plan := seeded seed (() => generateLevel depth)

-- Every plan the tests look at: each seed at each depth.
def plans: List Plan := seeds.flatMap (seed => (List.between 1 deepest).map (depth => planned seed depth))

-- Search

-- A cell as one number, to keep the cells seen in a `Set`.
def keyOf (position: Position): Nat := position.row * levelColumns + position.column

-- The cells that can be walked to from `start`, by a depth-first search
-- over the cells that aren't walls. Each cell is pushed once, when first
-- seen, so the search ends within as many steps as there are cells.
def reachableFrom (level: Level) (start: Position): Set Nat :=
  explore level (levelRows * levelColumns + 1) [start] (Set.singleton (keyOf start))

def explore (level: Level): Nat → List Position → Set Nat → Set Nat
  | 0, pending, seen => seen
  | Succ fuel, [], seen => seen
  | Succ fuel, Cons cell pending, seen =>
    let fresh := [North, South, West, East].map cell.toward |> .filter (next => ¬isWall level next ∧ ¬seen.contains (keyOf next))
    explore level fuel (fresh ++ pending) (fresh.foldLeft seen (cells next => cells.insert (keyOf next)))

def canReachGoal (level: Level): Bool := (reachableFrom level level.start).contains (keyOf level.goal)

-- Every floor cell can be reached, not only the goal: no room is cut off.
def allFloorReachable (level: Level): Bool :=
  let reached := reachableFrom level level.start
  (List.range levelRows).all (row => (List.range levelColumns).all (column => isWall level { row, column } ∨ reached.contains (keyOf { row, column })))

-- An area lies inside the screen, with rock all round the edge.
def fitsOnScreen (area: Area): Bool :=
  1 ≤ area.corner.row ∧ area.corner.row + area.down + 2 ≤ levelRows ∧ 1 ≤ area.corner.column ∧ area.corner.column + area.across + 2 ≤ levelColumns

test "the search finds a cell next door, and not one through rock" :=
  let level := testLevel
  let reached := reachableFrom level corner
  reached.contains (keyOf { row = 1, column = 2 }) ∧ reached.contains (keyOf { row = 3, column = 24 }) ∧ ¬reached.contains (keyOf { row = 2, column = 15 })
test "the search doesn't cross rock" := ¬canReachGoal { testLevel | corridors = [] }

-- Every level can be played

test "the goal can be reached from the start, on every seed and depth" := plans.all (plan => canReachGoal plan.level)
test "every floor cell can be reached" := (seeds.take 10).all (seed => allFloorReachable (planned seed 1).level)
test "the start and the goal are different cells, in different rooms" :=
  plans.all (plan => plan.level.start ≠ plan.level.goal ∧ ¬plan.level.exit.contains plan.level.start)
test "every room and corridor fits on the screen" := plans.all (plan => (plan.level.rooms ++ plan.level.corridors).all fitsOnScreen)
test "six rooms" := plans.all (plan => plan.level.rooms.length == 6)
test "the terrain is drawn at the size of the screen" :=
  plans.all (plan => plan.level.terrain.length == levelRows ∧ plan.level.terrain.all (row => row.length == levelColumns))
test "the start is floor and the goal is stairs, but not on the deepest level" :=
  plans.all (plan => ¬isWall plan.level plan.level.start ∧ isStairs plan.level plan.level.goal == (plan.level.depth < deepest))
test "different seeds make different levels" := (seeds.map (seed => (planned seed 1).level.entrance)).dedup.length > 30

-- Monsters and items are placed where they may stand

def arrived (plan: Plan): State := startingState plan []

test "no monster is placed in a wall or on the player" :=
  plans.all (plan =>
    let state := arrived plan
    state.monsters.all (monster => ¬isWall state.level monster.position ∧ monster.position ≠ state.player))
test "no two monsters share a cell" :=
  plans.all (plan => (arrived plan).monsters.map (.position) |> .dedup |> .length == (arrived plan).monsters.length)
test "no item is placed in a wall, on the player, or on the stairs" :=
  plans.all (plan =>
    let state := arrived plan
    state.items.all (item => ¬isWall state.level item.position ∧ item.position ≠ state.player ∧ ¬isStairs state.level item.position))
test "nearly every planned monster is placed" :=
  let placed := plans.sumBy (plan => (arrived plan).monsters.length)
  let wanted := plans.sumBy (plan => plan.monsters.length)
  placed * 10 ≥ wanted * 9
test "monsters start out of reach: none next to the player" :=
  plans.all (plan => (arrived plan).monsters.all (monster => monster.position.distance plan.level.start > 1))

-- Deeper is harder, and the amulet is at the bottom

def kindsAt (depth: Nat): List Kind := seeds.flatMap (seed => (planned seed depth).monsters.map (.kind))

test "more monsters further down" := [1, 2, 3].map (depth => (planned 5 depth).monsters.length) == [4, 6, 8]
test "no trolls on the first level" := (kindsAt 1).all (kind => kind ≠ Troll)
test "more trolls on the bottom level than goblins" := (kindsAt 3).count (== Troll) > (kindsAt 3).count (== Goblin)
test "the amulet lies at the goal of the bottom level, and only there" :=
  plans.all (plan =>
    let amulets := (arrived plan).items.filter (item => item.loot == Amulet)
    if plan.level.depth == deepest then amulets.map (.position) == [plan.level.goal] else amulets == [])
test "a sword on each level above the bottom" :=
  plans.all (plan => plan.items.any (item => item.loot == Sword) == (plan.level.depth < deepest))

-- A new game

test "a new game starts on the first level, with the two below made" :=
  let state := seeded defaultSeed newGame
  state.level.depth == 1 ∧ state.below.map (plan => plan.level.depth) == [2, 3] ∧ state.player == state.level.start

-- Placing by hand

def deeperPlan: Plan := {
  level = Level.build 2 roomB roomA [roomA, roomB] [corridor],
  monsters = [
    { kind = Orc, position = roomB.middle, hitPoints = 7 },
    { kind = Orc, position = { row = 0, column = 0 }, hitPoints = 7 },
    { kind = Goblin, position = { row = 1, column = 2 }, hitPoints = 3 },
    { kind = Troll, position = { row = 1, column = 2 }, hitPoints = 12 }
  ],
  items = [
    { loot = Potion, position = roomB.middle },
    { loot = Potion, position = { row = 2, column = 15 } },
    { loot = Sword, position = { row = 1, column = 3 } },
    { loot = Potion, position = { row = 1, column = 3 } },
    { loot = Potion, position = roomA.middle }
  ]
}

test "arriving keeps the monsters that may stand where they were planned" :=
  (arrive quiet deeperPlan).monsters == [{ kind = Goblin, position = { row = 1, column = 2 }, hitPoints = 3 }]
test "and the items" :=
  (arrive quiet deeperPlan).items == [({ loot = Sword, position = { row = 1, column = 3 } }: Item)]
test "arriving puts the player at the new level's start" := (arrive quiet deeperPlan).player == roomB.middle
