-- Advent of Code 2024, day 3: corrupted memory with instructions like
-- `mul(44,46)` scattered through noise. Part 1 adds up the products of every
-- well-formed `mul`; part 2 also obeys `do()` and `don't()`, which turn the
-- `mul`s after them on and off.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day03.main < inputs/2024/day03.txt
--
-- The proofs are in `Aoc.Year2024.Day03.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day03.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day03
import Std (Bool, Fail, IO, List, Nat, Option, Parse, Text)
import Std.Parse (char, findAll, nat, oneOf, pick, text)

def main(): {IO, Fail} () :=
  let instructions := parseInstructions IO.readAll()
  IO.print "Part 1: ${solvePart1 instructions}"
  IO.print "Part 2: ${solvePart2 instructions}"

-- An uncorrupted instruction.
type Instruction =
  | Mul (left: Nat) (right: Nat)
  | Do
  | Dont

-- A number of one to three digits.
def shortNumber(): {Parse} Nat :=
  let start := Parse.mark()
  let number := nat()
  let finish := Parse.mark()
  Parse.ensure (finish.offset - start.offset ≤ 3) "expected at most three digits"
  number

-- "mul(44,46)", "do()" or "don't()", exactly: no spaces, no other brackets.
def instruction(): {Parse} Instruction :=
  oneOf [
    () =>
      text "mul("
      let left := shortNumber()
      char ','
      let right := shortNumber()
      char ')'
      Mul left right,
    () => pick [("do()", Do), ("don't()", Dont)]
  ]

-- Every instruction in the memory, in order; everything else is noise.
def parseInstructions (memory: Text): {Fail} (List Instruction) := Parse.all memory (() => findAll instruction)

-- What a `mul` adds; `do()` and `don't()` add nothing.
def result: Instruction → Nat
  | Mul left right => left * right
  | Do => 0
  | Dont => 0

def solvePart1 (instructions: List Instruction): Nat := instructions.sumBy result

-- Part 2's running state: whether `mul` is enabled, and the sum so far.
type Tally = { enabled: Bool, total: Nat }

def step (tally: Tally): Instruction → Tally
  | Mul left right => if tally.enabled then { tally | total = tally.total + left * right } else tally
  | Do => { tally | enabled = True }
  | Dont => { tally | enabled = False }

-- `mul` starts enabled.
def solvePart2 (instructions: List Instruction): Nat :=
  instructions.foldLeft ({ enabled = True, total = 0 }: Tally) step |> .total
