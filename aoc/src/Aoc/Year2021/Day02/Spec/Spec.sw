--| Day 2 as the puzzle states it: the submarine starts at the surface, at
--| horizontal position 0, and follows the commands one at a time. The proofs
--| (Proofs/) show the program computes the same answers, for every list of
--| commands.
--|
--| Depth and aim are `Int`s, so `up` always takes the submarine up by its
--| units: nothing here stops at the surface (the puzzle never says what
--| happens there, and its inputs never go above it).

namespace Aoc.Year2021.Day02.Spec
import Aoc.Year2021.Day02 (Command)
import Std (Int, List)

--| Part 1's submarine: how far it has gone, and how deep it is.
type Submarine = { horizontal: Nat, depth: Int }

--| Part 1: `forward X` increases the horizontal position by X; `down X`
--| increases the depth by X; `up X` decreases it by X.
def Submarine.follow (submarine: Submarine): Command → Submarine
  | Forward units => { horizontal = submarine.horizontal + units, depth = submarine.depth }
  | Down units => { horizontal = submarine.horizontal, depth = submarine.depth + units.toInt }
  | Up units => { horizontal = submarine.horizontal, depth = submarine.depth - units.toInt }

--| Follow the commands in order from the surface, and multiply the final
--| horizontal position by the final depth.
def part1 (commands: List Command): Int :=
  let final := commands.foldLeft { horizontal = 0, depth = 0 } Submarine.follow
  final.horizontal.toInt * final.depth

--| Part 2's submarine also has an aim, 0 at the start.
type AimedSubmarine = { horizontal: Nat, depth: Int, aim: Int }

--| Part 2: `down X` increases the aim by X; `up X` decreases it by X;
--| `forward X` increases the horizontal position by X and the depth by the aim
--| times X.
def AimedSubmarine.follow (submarine: AimedSubmarine): Command → AimedSubmarine
  | Forward units => {
    horizontal = submarine.horizontal + units,
    depth = submarine.depth + submarine.aim * units.toInt,
    aim = submarine.aim
  }
  | Down units => { horizontal = submarine.horizontal, depth = submarine.depth, aim = submarine.aim + units.toInt }
  | Up units => { horizontal = submarine.horizontal, depth = submarine.depth, aim = submarine.aim - units.toInt }

--| The same, with the part 2 submarine.
def part2 (commands: List Command): Int :=
  let final := commands.foldLeft { horizontal = 0, depth = 0, aim = 0 } AimedSubmarine.follow
  final.horizontal.toInt * final.depth
