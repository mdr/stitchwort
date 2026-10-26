-- Unit tests of one turn: movement, walls, combat, chasing, items, the
-- stairs and the end of the game. Each uses `resolve` with fixed dice, so
-- the rolls are known: with seed 0 the player's blow does 2 and a goblin's
-- 1, with seed 1 the player's does 3, and with seed 2 it does 4.
--
-- The level is made by hand: two rooms joined by a corridor along row 3,
-- with the stairs in the middle of the second.
--
--   ############       ############
--   #..........#       #..........#
--   #..........#       #..........#
--   #.......................>.....#
--   #..........#       #..........#
--   #..........#       #..........#
--   ############       ############

namespace Rogue.Tests
import Rogue (..)
import Std (List, Text)

-- Rows 1 to 5, columns 1 to 10.
def roomA: Area := { corner = { row = 1, column = 1 }, down = 4, across = 9 }

-- Rows 1 to 5, columns 20 to 29.
def roomB: Area := { corner = { row = 1, column = 20 }, down = 4, across = 9 }

-- Row 3, from column 10 to 20.
def corridor: Area := { corner = { row = 3, column = 10 }, down = 0, across = 10 }

def testLevel: Level := Level.build 1 roomA roomB [roomA, roomB] [corridor]

-- The top-left corner of the first room.
def corner: Position := { row = 1, column = 1 }

-- The test level with nothing else about.
def quiet: State := {
  level = testLevel,
  player = corner,
  hitPoints = maxHitPoints,
  potions = 0,
  strength = startingStrength,
  monsters = [],
  items = [],
  turn = 0,
  message = "",
  phase = Playing
}

def lowRoll: Dice := { seed = 0 }
def middleRoll: Dice := { seed = 1 }
def highRoll: Dice := { seed = 2 }

test "the rolls the tests rely on" :=
  lowRoll.upTo 0 2 == 0 ∧ middleRoll.upTo 0 2 == 1 ∧ highRoll.upTo 0 2 == 2 ∧ lowRoll.upTo 1 1 == 0 ∧ lowRoll.upTo 1 2 == 1

-- Walls

test "a wall above blocks the way" := (resolve lowRoll quiet (Move North)).player == corner
test "a wall to the left blocks the way" := (resolve lowRoll quiet (Move West)).player == corner
test "being blocked says so" := (resolve lowRoll quiet (Move North)).message == "A wall blocks your way."
test "being blocked still takes a turn" := (resolve lowRoll quiet (Move North)).turn == 1
test "an open cell lets you through" := (resolve lowRoll quiet (Move East)).player == { row = 1, column = 2 }
test "south too" := (resolve lowRoll quiet (Move South)).player == { row = 2, column = 1 }
test "a corridor leads out of a room" :=
  let atDoor := { quiet | player = { row = 3, column = 10 } }
  (resolve lowRoll atDoor (Move East)).player == { row = 3, column = 11 }
test "a corridor has rock on both sides" :=
  let inCorridor := { quiet | player = { row = 3, column = 15 } }
  (resolve lowRoll inCorridor (Move North)).player == inCorridor.player ∧ (resolve lowRoll inCorridor (Move South)).player == inCorridor.player
test "walls are outside the rooms and corridors" :=
  isWall testLevel { row = 0, column = 0 } ∧ isWall testLevel { row = 2, column = 15 } ∧ ¬isWall testLevel corner ∧ ¬isWall testLevel { row = 3, column = 15 }
test "past the map is wall" := isWall testLevel { row = 50, column = 3 } ∧ isWall testLevel { row = 3, column = 500 }

-- Combat

def goblinNextDoor: Monster := { kind = Goblin, position = { row = 1, column = 2 }, hitPoints = 3 }

def facingGoblin: State := { quiet | monsters = [goblinNextDoor] }

test "bumping a monster attacks it instead of moving" := (resolve lowRoll facingGoblin (Move East)).player == corner
test "a blow of 2 leaves a goblin with 1" := (resolve lowRoll facingGoblin (Move East)).monsters == [{ goblinNextDoor | hitPoints = 1 }]
test "a blow of 3 kills a goblin" := (resolve middleRoll facingGoblin (Move East)).monsters == []
test "a blow of 4 kills a goblin too" := (resolve highRoll facingGoblin (Move East)).monsters == []
test "a goblin hits back" := (resolve lowRoll facingGoblin (Move East)).hitPoints == maxHitPoints - 1
test "the message tells both blows" :=
  (resolve lowRoll facingGoblin (Move East)).message == "You hit the goblin for 2. The goblin hits you for 1."
test "a dead goblin doesn't hit back" := (resolve middleRoll facingGoblin (Move East)).hitPoints == maxHitPoints
test "killing says so" := (resolve middleRoll facingGoblin (Move East)).message == "You kill the goblin!"
test "the blow lands only on the monster bumped" :=
  let far: Monster := { kind = Orc, position = { row = 3, column = 7 }, hitPoints = 7 }
  let after := resolve lowRoll { facingGoblin | monsters = [goblinNextDoor, far] } (Move East)
  after.monsters.map (.hitPoints) == [1, 7]

def orcNextDoor: Monster := { kind = Orc, position = { row = 1, column = 2 }, hitPoints = 7 }

test "an orc hits harder" := (resolve lowRoll { quiet | monsters = [orcNextDoor] } Wait).hitPoints == maxHitPoints - 2
test "a troll harder still" :=
  (resolve lowRoll { quiet | monsters = [{ orcNextDoor | kind = Troll, hitPoints = 12 }] } Wait).hitPoints == maxHitPoints - 3
test "losing the last hit points ends the game" :=
  let after := resolve lowRoll { quiet | monsters = [orcNextDoor], hitPoints = 1 } Wait
  after.phase == Died ∧ after.hitPoints == 0
test "damage stops at zero" := (resolve lowRoll { quiet | monsters = [orcNextDoor], hitPoints = 1 } Wait).message == "You wait. The orc hits you for 2. You die..."

-- Chasing

def stumbles (dice: Dice): Bool := dice.chance 2 5

-- Where a lone monster is after the player waits a turn.
def chased (dice: Dice) (player: Position) (monster: Monster): List Position :=
  (resolve dice { quiet | player, monsters = [monster] } Wait).monsters.map (.position)

def goblinAt (position: Position): Monster := { kind = Goblin, position, hitPoints = 3 }

test "a monster that sees the player closes in, unless it stumbles" :=
  (List.range 20).all (seed => stumbles { seed } ∨ chased { seed } corner (goblinAt { row = 1, column = 4 }) == [{ row = 1, column = 3 }])
test "most monsters don't stumble" := (List.range 20).count (seed => stumbles { seed }) < 8
test "a chasing monster closes the longer gap first" :=
  (List.range 20).all (seed => stumbles { seed } ∨ chased { seed } corner (goblinAt { row = 5, column = 2 }) == [{ row = 4, column = 2 }])
test "a chasing monster goes round rock" :=
  let player: Position := { row = 1, column = 10 }
  (List.range 20).all (seed => stumbles { seed } ∨ chased { seed } player (goblinAt { row = 3, column = 11 }) == [{ row = 3, column = 10 }])
test "a chasing monster follows the player down a corridor" :=
  let player: Position := { row = 3, column = 12 }
  (List.range 20).all (seed => stumbles { seed } ∨ chased { seed } player (goblinAt { row = 3, column = 17 }) == [{ row = 3, column = 16 }])
test "a monster out of sight doesn't give chase" :=
  let far := goblinAt roomB.middle
  let closer := (dice: Dice) => (chased dice corner far).all (position => position.distance corner < far.position.distance corner)
  (List.range 20).count (seed => closer { seed }) < 10
test "a monster won't step onto another" :=
  let first := goblinAt { row = 1, column = 3 }
  let second := goblinAt { row = 1, column = 4 }
  let after := resolve lowRoll { quiet | monsters = [second, first] } Wait
  (after.monsters.map (.position)).dedup.length == 2
test "monsters chase together without sharing a cell" :=
  let pack := [goblinAt { row = 1, column = 5 }, goblinAt { row = 2, column = 5 }, goblinAt { row = 1, column = 6 }]
  (List.range 20).all (seed =>
    let after := resolve { seed } { quiet | monsters = pack } Wait
    after.monsters.map (.position) |> .dedup |> .length == 3)

-- Items

def lying (loot: Loot): State := { quiet | items = [{ loot, position = { row = 1, column = 2 } }] }

test "walking onto a potion picks it up" :=
  let after := resolve lowRoll (lying Potion) (Move East)
  after.potions == 1 ∧ after.items == [] ∧ after.message == "You pick up a potion."
test "picking up doesn't heal" := (resolve lowRoll { lying Potion | hitPoints = 3 } (Move East)).hitPoints == 3
test "drinking a potion heals" :=
  let after := resolve lowRoll { quiet | potions = 2, hitPoints = 3 } Drink
  after.hitPoints == 8 ∧ after.potions == 1 ∧ after.turn == 1
test "a potion heals no further than the maximum" := (resolve lowRoll { quiet | potions = 1, hitPoints = 10 } Drink).hitPoints == maxHitPoints
test "with no potions, drinking says so and takes no time" :=
  let after := resolve lowRoll { facingGoblin | hitPoints = 3 } Drink
  after.message == "You have no potions." ∧ after.turn == 0 ∧ after.hitPoints == 3
test "monsters act while you drink" := (resolve lowRoll { facingGoblin | potions = 1, hitPoints = 3 } Drink).hitPoints == 7

-- The damage left on an orc after one blow, for each of 40 rolls.
def orcAfterBlows (state: State): List Nat :=
  let facingOrc := { state | monsters = [{ orcNextDoor | kind = Orc }] }
  (List.range 40).map (seed => (resolve { seed } facingOrc (Move East)).monsters.map (.hitPoints) |> .headOr 0)

test "a sword raises the player's strength" :=
  let after := resolve lowRoll (lying Sword) (Move East)
  after.strength == startingStrength + swordBonus ∧ after.items == [] ∧ after.message == "You wield a sharper sword: your blows now do up to 6."
test "without a sword, a blow does at most 4" := (orcAfterBlows quiet).all (left => left ≥ 3)
test "with a sword, some blows do more" := (orcAfterBlows { quiet | strength = 6 }).any (left => left < 3)
test "taking the amulet wins, and the monsters don't act" :=
  let after := resolve lowRoll { lying Amulet | monsters = [goblinAt { row = 2, column = 2 }] } (Move East)
  after.phase == Won ∧ after.hitPoints == maxHitPoints ∧ after.message == "You take the amulet. You win!"
test "items are drawn, under monsters" :=
  let state := { lying Sword | items = [{ loot = Potion, position = { row = 1, column = 3 } }, { loot = Sword, position = { row = 1, column = 2 } }], monsters = [goblinAt { row = 1, column = 3 }] }
  (render state).get 1 == Some ("#@)g.......#       #..........#".padRight levelColumns ' ')

-- The stairs

def onStairs: State := { quiet | player = testLevel.goal }

test "the stairs are at the goal, and drawn" := isStairs testLevel { row = 3, column = 24 } ∧ (render quiet).get 3 == Some ("#.......................>.....#".padRight levelColumns ' ')
test "> on the stairs goes down" :=
  let after := resolve lowRoll onStairs Descend
  after.level.depth == 2 ∧ after.player == after.level.start ∧ after.message == "You go down the stairs to level 2."
test "going down keeps what the player carries" :=
  let after := resolve lowRoll { onStairs | potions = 2, strength = 6, hitPoints = 5 } Descend
  after.potions == 2 ∧ after.strength == 6 ∧ after.hitPoints == 5
test "> away from the stairs does nothing, and takes no time" :=
  let after := resolve lowRoll quiet Descend
  after.level == testLevel ∧ after.turn == 0 ∧ after.message == "There are no stairs here."
test "the deepest level has no stairs" := ¬isStairs { testLevel | depth = deepest } testLevel.goal

-- Giving up, and after the end

test "quitting gives up" := (resolve lowRoll quiet Quit).phase == GaveUp
test "nothing happens once the game is over" :=
  let over := { facingGoblin | phase = Died }
  resolve lowRoll over (Move East) == over ∧ resolve lowRoll { over | phase = Won } Wait == { over | phase = Won }

-- Keys

test "vi keys" := ['h', 'j', 'k', 'l'].map commandOfChar == [Some (Move West), Some (Move South), Some (Move North), Some (Move East)]
test "wasd keys" := ['a', 's', 'w', 'd'].map commandOfChar == [Some (Move West), Some (Move South), Some (Move North), Some (Move East)]
test "other keys" := ['.', '>', 'p', 'q', 'x', ' '].map commandOfChar == [Some Wait, Some Descend, Some Drink, Some Quit, None, None]

-- Randomness

test "the generator is the C example's" := lcg 1 == 1103527590
test "seeded answers from the generator" := seeded 1 (() => [next(), next()]) == [lcg 1 / 65536, lcg (lcg 1) / 65536]
test "roll stays in range" := seeded 3 (() => (List.range 50).map (_ => roll 4)) |> .all (number => number ≤ 4)
test "the same seed gives the same game" := seeded 7 (() => step facingGoblin Wait) == seeded 7 (() => step facingGoblin Wait)
test "a step is resolve with the seeded dice" := seeded 7 (() => step facingGoblin (Move East)) == resolve { seed = lcg 7 / 65536 } facingGoblin (Move East)
