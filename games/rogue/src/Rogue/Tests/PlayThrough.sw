-- Whole games through `Terminal.simulate`: scripted keys, a fixed seed,
-- and the frames the game draws. One more runs the whole `main` through
-- `IO.simulate`, with `Terminal.toIO` decoding piped bytes.

namespace Rogue.Tests
import Rogue (..)
import Std (Ansi, IO, Key, List, Pair, Terminal, Text)
import Std.Key (Printable, Up, Down, Left, Right, Unknown, Enter)

-- The seed the tests play on (the game's own comes from `IO.randomSeed`).
def testSeed: Nat := 2026

-- The keys of some text, one per character.
def keysOf (text: Text): List Key := text.toList.map Printable

-- A winning game on the test seed, a line or two per level: collect the
-- sword and potions, take the stairs (`>`), fight what's in the way,
-- drink (`p`) when hurt, and take the amulet on level 3.
def winningRoute: Text := Text.join [
  "kjllllllllllllllllllllllllljjjjjjjjjjjhjhhhh",
  "hhhhhhhhhhhhhhkkkjjjllllllllllllllllllll>jjl",
  "lljjjjjjjjhhhhhhhhhhhhhhjhhhhhhhhphhhhhhhhhh",
  "hhhhhhhhhhhjpjjjjjkhhhhhhhhklll>llllllllllll",
  "llllllllkkkllllllllllllplllllllllllklkppllll",
  "lpjhhhhh"
] ' '

-- The game as `main` plays it, on scripted keys and the test seed: the
-- frames drawn, and the final state.
def simulateGame (keys: List Key): {Partial} Pair (List (List Text)) State :=
  Terminal.simulate keys (() => Random.withSeed testSeed (() => playGame (newGame())))

def winningGame: {Partial} Pair (List (List Text)) State := simulateGame (keysOf winningRoute)

-- The status line of each frame drawn.
def statusLines (frames: List (List Text)): List Text := frames.filterMap (frame => frame.get levelRows)

test "the winning route takes the amulet" := winningGame.snd.phase == Won
test "on level 3, on turn 228, with 8 hit points" :=
  let final := winningGame.snd
  final.level.depth == 3 ∧ final.turn == 228 ∧ final.hitPoints == 8
test "it picks up both swords on the way" := winningGame.snd.strength == startingStrength + 2 * swordBonus
test "every level is visited, in order" :=
  let depths := statusLines winningGame.fst |> .map (line => line.take 11) |> .dedup
  depths == ["Level 1/3  ", "Level 2/3  ", "Level 3/3  "]
test "going down says so" := winningGame.fst.any (frame => frame.last == Some "You go down the stairs to level 3.")
test "one frame per turn, and the first" := winningGame.fst.length == 229
test "the end of the keys gives up" := (simulateGame []).snd.phase == GaveUp
test "q gives up" :=
  let (frames, final) := simulateGame (keysOf "qlll")
  final.phase == GaveUp ∧ final.turn == 0 ∧ frames.length == 2
test "keys that aren't commands are skipped, with no frame" :=
  let (frames, final) := simulateGame [Printable 'x', Unknown, Enter, Printable '.', Printable '?', Printable '.']
  final.turn == 2 ∧ frames.length == 4
test "the arrows move" :=
  let start := simulateGame [] |> .snd |> .player
  let moved := simulateGame [Right, Right, Left, Down, Up, Right] |> .snd |> .player
  moved == { start | column = start.column + 2 }
test "the arrows, as commands" := [Up, Down, Left, Right].map commandOf == [Some (Move North), Some (Move South), Some (Move West), Some (Move East)]
test "other keys aren't commands" := [Unknown, Enter, Key.Escape, Printable 'x'].map commandOf == [None, None, None, None]

-- The whole `main` on piped input, through `IO.simulate` and
-- `Terminal.toIO`: the bytes are decoded as keys (an arrow's escape
-- sequence included), each frame is printed as lines with a form feed
-- after it, and the seed is `IO.simulate`'s 0.
test "main on piped input" :=
  let (printed, _) := IO.simulate ["l\u{1b}[Cxq"] main
  (printed.filter (line => line == "\u{c}")).length == 4 ∧ printed.last == Some "You gave up on level 1, on turn 2."
test "the winning route through the console handler" :=
  let (printed, final) := IO.simulate [winningRoute] (() => playOn testSeed)
  final.phase == Won ∧ (printed.filter (line => line == "\u{c}")).length == 229

-- `IO.simulateWith` gives `main` the seed the route was found on, so the real
-- `main` plays it through to the win.
test "main plays the winning route on seed 2026" :=
  let (printed, _) := IO.simulateWith testSeed [winningRoute] main
  (printed.filter (line => line == "\u{c}")).length == 229 ∧ (printed.last |> .getOrElse "").startsWith "You won"

-- The first level on the test seed. The bars mark the ends of each row,
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

test "the first frame draws the first level" :=
  let lines := simulateGame [] |> .fst |> .head |> .getOrElse []
  lines.take levelRows |> .map (row => "|${row}|") == firstMap.lines ∧
    lines.drop levelRows == ["Level 1/3   HP 12/12   Potions 0   Blows 2-4   Turn 0", keysLine, "Find the amulet, 3 levels down."]

test "the frame is the rendered text, coloured" :=
  let state := Random.withSeed testSeed newGame
  (frame state).map Ansi.strip == render state ∧ frame state != render state
test "the player is bold yellow" := paint '@' == "\u{1b}[1m\u{1b}[33m@\u{1b}[39m\u{1b}[22m"
