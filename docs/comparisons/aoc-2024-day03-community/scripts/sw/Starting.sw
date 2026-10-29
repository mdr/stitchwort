-- Day 3 with `findAllStarting`: the noise between an `m` or a `d` is
-- skipped with one `span`, not tried a character at a time.
namespace Scratch.Starting
import Aoc.Year2024.Day03 (Instruction, instruction, solvePart1, solvePart2)
import Std (Fail, IO, List, Parse, Text)
import Std.Parse (findAllStarting)

def main(): {IO, Fail} () :=
  let instructions := Parse.all IO.readAll() (() => findAllStarting (char => char == 'm' ∨ char == 'd') instruction)
  IO.print "Part 1: ${solvePart1 instructions}"
  IO.print "Part 2: ${solvePart2 instructions}"
