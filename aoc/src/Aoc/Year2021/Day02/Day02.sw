--| Advent of Code 2021, day 2: a submarine follows a list of commands, one per
--| line: `forward 5`, `down 3`, `up 2`. Part 1 reads them plainly: forward
--| moves it ahead, down and up change its depth. Part 2 reads down and up as
--| tilting its aim instead, and forward as moving ahead and sinking by the aim
--| times the distance. Each part's answer is the final horizontal position
--| times the final depth.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day02.main < inputs/2021/day02.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| The program doesn't steer the submarine one command at a time: the
--| horizontal position is the sum of the forward moves, part 1's depth the sum
--| of the downs less the ups, and part 2's aim before each command is a
--| running sum, so its depth is the sum of each forward move times the aim it
--| is made at. Depth and aim are `Int`s: the puzzle never says they stay above
--| zero, and an `up` past the surface is followed as it is written. The proofs
--| that both answers are those of the step-by-step submarine, for every list
--| of commands, are in `Aoc.Year2021.Day02.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2021.Day02.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day02
import Std (Fail, IO, Int, List, Parse)
import Std.Parse (label, nat, pick, spaces, spaces1)

def main(): {IO, Fail} () :=
  let commands := parseCommands IO.readAll()
  IO.print "Part 1: ${solvePart1 commands}"
  IO.print "Part 2: ${solvePart2 commands}"

type Command = | Forward (units: Nat) | Down (units: Nat) | Up (units: Nat)

--| One command per line. Spaces around a command are allowed; anything else
--| fails, naming the line and column.
def parseCommands (input: Text): {Fail} List Command := Parse.eachLine input command

--| "forward 5" is `Forward 5`.
def command(): {Parse} Command :=
  spaces()
  let direction := label "forward, down or up" (() => pick [("forward", Forward), ("down", Down), ("up", Up)])
  spaces1()
  let units := nat()
  spaces()
  direction units

--| How far a command moves the submarine ahead.
def Command.ahead: Command → Nat
  | Forward units => units
  | Down units => 0
  | Up units => 0

--| How far a command takes it down (part 1's depth, part 2's aim); `up` is
--| negative.
def Command.down: Command → Int
  | Forward units => 0
  | Down units => units.toInt
  | Up units => -units.toInt

--| The horizontal position at the end, the same in both parts.
def horizontal (commands: List Command): Nat := commands.sumBy .ahead

--| Part 1: horizontal position times depth.
def solvePart1 (commands: List Command): Int := (horizontal commands).toInt * commands.sumBy .down

--| Part 2: the aim before each command is the sum of the downs before it, and
--| each forward move sinks the submarine by the aim it is made at times its
--| length.
def solvePart2 (commands: List Command): Int := (horizontal commands).toInt * aimedDepth 0 commands

--| The depth the commands sink the submarine by, starting at aim `aim`.
def aimedDepth (aim: Int) (commands: List Command): Int :=
  commands
    |> .scanLeft aim (aimSoFar command => aimSoFar + command.down)
    |> .zipWith commands (aimThen command => aimThen * command.ahead.toInt)
    |> .sum
