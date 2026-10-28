-- Day 3's tests: the puzzle's examples and unit tests. Kept apart from the
-- program, so `stitchwort run Aoc.Year2024.Day03.main` doesn't check them.

namespace Aoc.Year2024.Day03.Tests
import Aoc.Year2024.Day03 (..)
import Std (Fail, List, Nat, Parse, Result, Text)

def parsed (memory: Text): Result (List Instruction) Text := Fail.toResult (() => parseInstructions memory)

def found (memory: Text): List Instruction := parsed memory |> .getOrElse []

-- The error from parsing `memory` as exactly one instruction.
def instructionError (memory: Text): Text := Fail.toResult (() => Parse.line memory instruction) |> .errorOrElse ""

-- Part 2's example adds a `don't()` and a `do()` to part 1's.
def example1: Text := "xmul(2,4)%&mul[3,7]!@^do_not_mul(5,5)+mul(32,64]then(mul(11,8)mul(8,5))"

def example2: Text := "xmul(2,4)&mul[3,7]!^don't()_mul(5,5)+mul(32,64](mul(11,8)undo()?mul(8,5))"

test "example, part 1" := solvePart1 (found example1) == 161
test "example, part 2" := solvePart2 (found example2) == 48
test "example, the instructions found" := found example1 == [Mul 2 4, Mul 5 5, Mul 11 8, Mul 8 5]
test "part 2's example, the instructions found" := found example2 == [Mul 2 4, Dont, Mul 5 5, Mul 11 8, Do, Mul 8 5]
test "part 2's example, part 1" := solvePart1 (found example2) == 161
test "part 1's example has no don't, so part 2 agrees" := solvePart2 (found example1) == 161

test "the puzzle's non-instructions" := found "mul(4*mul(6,9!?(12,34)mul ( 2 , 4 )" == []
test "three digits" := found "mul(123,999)" == [Mul 123 999]
test "four digits is too many" := found "mul(1234,5)" == []
test "four digits, even with leading zeros" := found "mul(0012,5)" == []
test "no closing bracket" := found "mul(1,2" == []
test "no number" := found "mul(,2)" == []
test "spaces" := found "mul ( 1,2)mul(1, 2)" == []
test "a negative number" := found "mul(-1,2)" == []
test "nested" := found "mul(mul(2,3))" == [Mul 2 3]
test "nested in the second number" := found "mul(4,mul(2,3))" == [Mul 2 3]
test "back to back" := found "mul(1,2)mul(3,4)" == [Mul 1 2, Mul 3 4]
test "don't is not do" := found "don't()do()" == [Dont, Do]
test "a broken don't" := found "don't(do()" == [Do]
test "across lines" := found "mul(1,\n2)mul(3,4)\ndo()\n" == [Mul 3 4, Do]
test "empty memory" := found "" == []
test "only noise" := found "%&!@^" == []

test "part 2 starts enabled" := solvePart2 [Mul 2 3] == 6
test "don't disables" := solvePart2 [Dont, Mul 2 3] == 0
test "do enables again" := solvePart2 [Dont, Mul 2 3, Do, Mul 4 5] == 20
test "the most recent one applies" := solvePart2 [Do, Dont, Mul 2 3, Dont, Do, Mul 4 5] == 20

-- Error messages, from parsing exactly one instruction.
test "error, four digits" := instructionError "mul(1234,5)" == "column 5: expected a number of 1 to 3 digits"
test "error, no closing bracket" := instructionError "mul(1,2" == "column 8: expected ')'"
test "error, a space" := instructionError "mul ( 1,2)" == "column 1: expected 'mul(' or 'do()' or 'don't()'"
test "error, a square bracket" := instructionError "mul(32,64]" == "column 10: expected ')'"
