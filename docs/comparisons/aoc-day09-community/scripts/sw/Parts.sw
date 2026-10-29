-- Where the program's time goes: part 1 alone, and building the floor
-- (key lines, outside cells, the summed-area table) alone.

namespace Scratch.Parts
import Aoc.Year2025.Day09 (Floor, parseTiles, solvePart1)
import Std (Fail, IO, List, Nat, PrefixSums)

def mainPart1(): {IO, Fail} () :=
  let tiles := parseTiles IO.readAll()
  IO.print "Part 1: ${solvePart1 tiles}"

def mainFloor(): {IO, Fail} () :=
  let tiles := parseTiles IO.readAll()
  let floor := Floor.of tiles
  IO.print "Floor ${floor.columns.length} x ${floor.rows.length}, outside ${floor.outside.block 0 floor.rows.length 0 floor.columns.length}"

def mainParse(): {IO, Fail} () :=
  let tiles := parseTiles IO.readAll()
  IO.print "Tiles ${tiles.length}"
