--| Day 14's puzzle examples, the parser, and each mask rule on its own.

namespace Aoc.Year2020.Day14.Tests
import Aoc.Year2020.Day14 (..)
import Std (Fail, List, Result, Text)

def parsed (input: Text): Result Program Text := Fail.toResult (() => parseProgram input)

def part1 (input: Text): Result Nat Text := (parsed input).map (.valueSum)

def part2 (input: Text): Result Nat Text := (parsed input).map (.decodedSum)

--| Part 1's example. Its mask has 34 Xs, so part 2 would write each value
--| to 2 ^ 34 addresses: the puzzle gives no part 2 answer for it.
def example: Text := """
  mask = XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X
  mem[8] = 11
  mem[7] = 101
  mem[8] = 0
  """

def example2: Text := """
  mask = 000000000000000000000000000000X1001X
  mem[42] = 100
  mask = 00000000000000000000000000000000X0XX
  mem[26] = 1
  """

def mask (symbols: Text): Mask :=
  { bits = symbols.toList.map (symbol => if symbol == '1' then On else if symbol == 'X' then X else Off) }

test "the example, part 1" := part1 example == Ok 165
test "the example 2, part 1" := part1 example2 == Ok 51
test "the example 2, part 2" := part2 example2 == Ok 208

test "the example's instructions" :=
  (parsed example).map (.instructions)
    == Ok [SetMask (mask "XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X"), Write 8 11, Write 7 101, Write 8 0]

test "11 masked is 73" := (mask "XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X").applyTo 11 == 73
test "101 masked is unchanged" := (mask "XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X").applyTo 101 == 101
test "0 masked is 64" := (mask "XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X").applyTo 0 == 64
test "a mask clears bits above its width" := (mask "XX").applyTo 6 == 2

test "address 42 decodes to four addresses" :=
  (mask "000000000000000000000000000000X1001X").decode 42 == [26, 27, 58, 59]
test "address 26 decodes to eight addresses" :=
  (mask "00000000000000000000000000000000X0XX").decode 26 == [16, 17, 18, 19, 24, 25, 26, 27]
test "a mask without Xs decodes to one address" := (mask "0101").decode 9 == [13]

test "a later write wins" := part1 "mask = XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX\nmem[3] = 5\nmem[3] = 7" == Ok 7
test "a program must start with a mask" := not (parsed "mem[3] = 5").isOk
test "a mask has 36 bits" := not (parsed "mask = XX01\nmem[3] = 5").isOk
test "a mask has only 0, 1 and X" := not (parsed "mask = XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX2\nmem[3] = 5").isOk
