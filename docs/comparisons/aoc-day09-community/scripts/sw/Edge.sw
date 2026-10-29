-- The community's most common part 2 (NerdyPepper's Haskell): a rectangle is
-- good when no line of the loop passes through its open interior. Not
-- general: it accepts a rectangle wholly outside a concave loop.

namespace Scratch.Edge
import Aoc.Year2025.Day09 (Tile, largest, loopLines, pairArea, parseTiles, solvePart1)
import Std (Fail, IO, List, Nat)

-- The line stays out of the open interior of the rectangle with corners a, b.
def away (a: Tile) (b: Tile) (line: (Tile, Tile)): Bool :=
  Nat.max line.fst.x line.snd.x ≤ Nat.min a.x b.x
    ∨ Nat.min line.fst.x line.snd.x ≥ Nat.max a.x b.x
    ∨ Nat.max line.fst.y line.snd.y ≤ Nat.min a.y b.y
    ∨ Nat.min line.fst.y line.snd.y ≥ Nat.max a.y b.y

def solvePart2 (tiles: List Tile): Nat :=
  let lines := loopLines tiles
  tiles.pairs |> .filter (p => lines.all (away p.fst p.snd)) |> .map pairArea |> largest

def main(): {IO, Fail} () :=
  let tiles := parseTiles IO.readAll()
  IO.print "Part 1: ${solvePart1 tiles}"
  IO.print "Part 2: ${solvePart2 tiles}"
