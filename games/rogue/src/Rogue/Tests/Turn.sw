-- Unit tests of one turn: movement, walls, combat, potions, the stairs and
-- the end of the game. Each uses `resolve` with fixed dice, so the rolls are
-- known: with seed 0 the player's blow does 2 and a goblin's 1, with seed 1
-- the player's does 3, and with seed 2 it does 4.

namespace Rogue.Tests
import Rogue (..)
import Std (List)

-- The top-left corner of the first room, with nothing else about.
def corner: Position := { row = 1, column = 1 }

def quiet: State := { initialState | player = corner, monsters = [], potions = [] }

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
test "a door is open" :=
  let atDoor := { quiet | player = { row = 3, column = 8 } }
  (resolve lowRoll atDoor (Move East)).player == { row = 3, column = 9 }
test "walls are where the map has #" := isWall { row = 0, column = 0 } ∧ isWall { row = 4, column = 9 } ∧ ¬isWall corner
test "past the map is wall" := isWall { row = 50, column = 3 } ∧ isWall { row = 3, column = 500 }

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
test "losing the last hit points ends the game" :=
  let after := resolve lowRoll { quiet | monsters = [orcNextDoor], hitPoints = 1 } Wait
  after.phase == Died ∧ after.hitPoints == 0
test "damage stops at zero" := (resolve lowRoll { quiet | monsters = [orcNextDoor], hitPoints = 1 } Wait).message == "You wait. The orc hits you for 2. You die..."

-- Monsters moving

def stumbles (dice: Dice): Bool := dice.chance 2 5

test "a monster that sees the player closes in, unless it stumbles" :=
  let goblin: Monster := { kind = Goblin, position = { row = 1, column = 4 }, hitPoints = 3 }
  let closesIn := (dice: Dice) => (resolve dice { quiet | monsters = [goblin] } Wait).monsters.map (.position) == [{ row = 1, column = 3 }]
  (List.range 20).all (seed => stumbles { seed } ∨ closesIn { seed })
test "most monsters don't stumble" := (List.range 20).count (seed => stumbles { seed }) < 8
test "a monster won't step onto another" :=
  let first: Monster := { kind = Goblin, position = { row = 1, column = 3 }, hitPoints = 3 }
  let second: Monster := { kind = Goblin, position = { row = 1, column = 4 }, hitPoints = 3 }
  let after := resolve lowRoll { quiet | player = { row = 1, column = 1 }, monsters = [second, first] } Wait
  (after.monsters.map (.position)).dedup.length == 2

-- Potions

def potionNextDoor: State := { quiet | potions = [{ row = 1, column = 2 }] }

test "a potion heals" := (resolve lowRoll { potionNextDoor | hitPoints = 3 } (Move East)).hitPoints == 8
test "a potion heals no further than the maximum" := (resolve lowRoll { potionNextDoor | hitPoints = 10 } (Move East)).hitPoints == maxHitPoints
test "a potion is used up" := (resolve lowRoll potionNextDoor (Move East)).potions == []

-- Winning, giving up, and after the end

def besideStairs: State := { quiet | player = { row = 8, column = 38 } }

test "the stairs win the game" := (resolve lowRoll besideStairs (Move East)).phase == Escaped
test "quitting gives up" := (resolve lowRoll quiet Quit).phase == GaveUp
test "nothing happens once the game is over" :=
  let over := { facingGoblin | phase = Died }
  resolve lowRoll over (Move East) == over

-- Keys

test "vi keys" := ['h', 'j', 'k', 'l'].map commandOf == [Some (Move West), Some (Move South), Some (Move North), Some (Move East)]
test "wasd keys" := ['a', 's', 'w', 'd'].map commandOf == [Some (Move West), Some (Move South), Some (Move North), Some (Move East)]
test "other keys" := ['.', 'q', 'x', ' '].map commandOf == [Some Wait, Some Quit, None, None]

-- Randomness

test "the generator is the C example's" := lcg 1 == 1103527590
test "seeded answers from the generator" := seeded 1 (() => [next(), next()]) == [lcg 1 / 65536, lcg (lcg 1) / 65536]
test "the same seed gives the same game" := seeded 7 (() => step facingGoblin Wait) == seeded 7 (() => step facingGoblin Wait)
test "a step is resolve with the seeded dice" := seeded 7 (() => step facingGoblin (Move East)) == resolve { seed = lcg 7 / 65536 } facingGoblin (Move East)
