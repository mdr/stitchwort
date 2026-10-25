-- Whole games through `IO.simulate`: scripted input lines, the default seed,
-- and the frames and final words the game prints.

namespace Rogue.Tests
import Rogue (..)
import Std (IO, List, Text)

-- A winning game on the default seed, a line or two per level: collect the
-- sword and potions, take the stairs (`>`), fight what's in the way,
-- drink (`p`) when hurt, and take the amulet on level 3.
def winningRoute: List Text := [
  "kjlllllllllllllllllllllllllljjjjjjjjjjjhjhhh",
  "hhhhhhhhhhhhhhhkkkjjjlllllllllllllllllll>",
  "jhkkklkllllllllllllljkkllkkkkkkkhhhhhhhhhhhh",
  "jhhhhhhhhhhhhhhhhhhhhjhhhhhhhhpkhkkkllllllll",
  "jjhhhhh>",
  "jlllkhhhhhhhhhhhhhhhhhhhhhhhhhhhhphpphhphhhh",
  "hjjkhhh"
]

-- The game as `main` plays it, on scripted input: what it prints, and the
-- final state.
def simulateGame (input: List Text): (List Text, State) :=
  IO.simulate input (() => fromLines (() => seeded defaultSeed (() => playGame (newGame()))))

def winningGame: (List Text, State) := simulateGame winningRoute

-- The status lines of the frames printed.
def statusLines (frames: List Text): List Text := frames.filterMap (frame => frame.lines.get levelRows)

test "the winning route takes the amulet" := winningGame.snd.phase == Won
test "on level 3, on turn 232, with 8 hit points" :=
  let final := winningGame.snd
  final.level.depth == 3 ∧ final.turn == 232 ∧ final.hitPoints == 8 ∧ final.below == []
test "it picks up both swords on the way" := winningGame.snd.strength == startingStrength + 2 * swordBonus
test "every level is visited, in order" :=
  let depths := statusLines winningGame.fst |> .map (line => line.take 11) |> .dedup
  depths == ["Level 1/3  ", "Level 2/3  ", "Level 3/3  "]
test "going down says so" := winningGame.fst.any (frame => frame.endsWith "You go down the stairs to level 3.")
test "one frame per turn, and the first" := winningGame.fst.length == 233
test "main's last words" := (IO.simulate winningRoute main).fst.last == Some "You won on turn 232 with 8 hit points."
test "the end of the input gives up" := (IO.simulate [] main).fst.last == Some "You gave up on level 1, on turn 0."
test "q gives up" := (simulateGame ["q", "lll"]).snd.phase == GaveUp
test "keys that aren't commands are skipped" := (simulateGame ["x", "?.", "", "."]).snd.turn == 2
test "several commands on a line" := (simulateGame ["ll"]).snd.player == { row = 4, column = 32 }

-- The first level on the default seed. The bars mark the ends of each row,
-- which is 66 cells wide.
def firstMap: Text := """
  |                                                    #######       |
  |  ########                                          #.g...#       |
  |  #......#                 #######                  #.....#       |
  |  #....g......................)..#                  #.....#       |
  |  #......#.                #..@...........................#       |
  |  ########.                #.....#                  ###.###       |
  |          .                #######                     .          |
  |          .                                            .          |
  |          .                                            .          |
  |          .                                            .          |
  |          .                                            .          |
  |          .                                            .          |
  |          .                   ########                 .          |
  |      ####.#####              #.....!#                 .          |
  |      #.......o#              #......#             ####.#####     |
  |      #g.............................#             #..!.....#     |
  |      #........#              #........................>....#     |
  |      ##########              #......#             #........#     |
  |                              ########             #........#     |
  |                                                   ##########     |"""

test "the first frame clears the screen and draws the first level" :=
  let frame := (simulateGame []).fst.head |> .getOrElse ""
  let lines := (frame.stripPrefix clearScreen |> .getOrElse "").lines
  lines.take levelRows |> .map (row => "|${row}|") == firstMap.lines ∧
    lines.drop levelRows == ["Level 1/3   HP 12/12   Potions 0   Blows 2-4   Turn 0", keysLine, "Find the amulet, 3 levels down."]
