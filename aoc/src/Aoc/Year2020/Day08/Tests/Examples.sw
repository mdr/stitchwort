--| Day 8's puzzle example, the ways a run ends, and the parser's errors.

namespace Aoc.Year2020.Day08.Tests
import Aoc.Year2020.Day08 (..)
import Std (Fail, Int, List, Result, Text)

def parsed (input: Text): Result Program Text := Fail.toResult (() => parseProgram input)

def part1 (input: Text): Result Int Text := Fail.toResult (() => solvePart1 (parseProgram input))

def part2 (input: Text): Result Int Text := Fail.toResult (() => solvePart2 (parseProgram input))

def outcome (input: Text): Result Outcome Text := (parsed input).map (program => program.code.run)

def example: Text := """
  nop +0
  acc +1
  jmp +4
  acc +3
  jmp -3
  acc -99
  acc +1
  jmp -4
  acc +6
  """

test "example, the instructions" :=
  (parsed example).map (program => program.instructions.take 3)
    == Ok [{ operation = Nop, argument = 0 }, { operation = Acc, argument = 1 }, { operation = Jmp, argument = 4 }]
test "example, a negative argument" :=
  (parsed example).map (program => program.instructions.drop 5 |> .take 1 |> .map .argument) == Ok [-99]
test "example, part 1" := part1 example == Ok 5
test "example, part 2" := part2 example == Ok 8

test "running off the end terminates" := outcome "acc +2\nnop +0" == Ok (Terminates 2)
test "jumping just past the end terminates" := outcome "jmp +2\nacc +5" == Ok (Terminates 0)
test "jumping further is outside the code" := outcome "acc +1\njmp +2" == Ok (JumpsAway 1)
test "jumping before the start is outside the code" := outcome "acc +1\njmp -2" == Ok (JumpsAway 1)
test "jmp +0 runs itself again" := outcome "acc -3\njmp +0" == Ok (Loops (-3))
test "part 1 needs a loop" := part1 "acc +1" == Err "the boot code terminates, with the accumulator at 1"
test "a repair to nop" := part2 "acc +1\njmp +0\nacc +2" == Ok 3
test "a repair to jmp" := part2 "nop +2\njmp +0\nacc +4" == Ok 4
test "no repair helps" :=
  part2 "jmp +0\njmp +0\nacc +1\njmp -1" == Err "no repair of one jmp or nop makes the boot code terminate"

test "an argument's sign is optional" :=
  (parsed "acc 3").map (program => program.instructions) == Ok [{ operation = Acc, argument = 3 }]
test "an unknown operation" := parsed "mul +3" == Err "line 1, column 1: expected 'acc', 'jmp' or 'nop', got 'mul'"
test "a missing argument" := parsed "nop +" == Err "line 1, column 6: expected a number, got the end of the line"
