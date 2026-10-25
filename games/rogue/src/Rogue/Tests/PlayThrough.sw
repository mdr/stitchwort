-- Whole games through `IO.simulate`: scripted input lines, the default seed,
-- and the frames and final words the game prints.

namespace Rogue.Tests
import Rogue (..)
import Std (IO, List, Text)

-- Down the first room, east through two doors, past the potion room's
-- doorway, north, a fight with the orc, and down to the stairs.
def winningRoute: List Text := [
  "j",
  "lllllllllllll",
  "jjjjjj",
  "lllllllll",
  "kkkk",
  "llllllllllll",
  "hhhh",
  "llll",
  "jjj",
  "l"
]

-- The game as `main` plays it, on scripted input: what it prints, and the
-- final state.
def simulateGame (input: List Text): (List Text, State) :=
  IO.simulate input (() => fromLines (() => seeded defaultSeed (() => playGame initialState)))

test "the winning route escapes" := (simulateGame winningRoute).snd.phase == Escaped
test "after a fight with the orc" :=
  let final := (simulateGame winningRoute).snd
  final.turn == 57 ∧ final.hitPoints == 6 ∧ final.monsters.length == 2
test "one frame per turn, and the first" := (simulateGame winningRoute).fst.length == 58
test "main's last words" := (IO.simulate winningRoute main).fst.last == Some "You escaped on turn 57 with 6 hit points."
test "the end of the input gives up" := (IO.simulate [] main).fst.last == Some "You gave up on turn 0."
test "q gives up" := (simulateGame ["q", "lll"]).snd.phase == GaveUp
test "keys that aren't commands are skipped" := (simulateGame ["x", "?l", "", "l"]).snd.turn == 2
test "several commands on a line" := (simulateGame ["ll"]).snd.player == { row = 2, column = 5 }

def firstFrame: Text := """
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
  HP 12/12   Turn 0   Monsters 4   (h/j/k/l or a/s/w/d move, . waits, q quits)
  Find the stairs (>) and escape."""

test "the first frame clears the screen and draws the dungeon" := (simulateGame []).fst.head == Some (clearScreen ++ firstFrame)
