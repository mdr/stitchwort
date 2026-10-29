-- Day 3's part 2 by the common split trick: cut the memory at each
-- "don't()", keep the first piece whole, and from every later piece keep
-- what follows its first "do()". Part 1 of what is kept is part 2.
namespace Scratch.Split
import Aoc.Year2024.Day03 (parseInstructions, solvePart1)
import Std (Fail, IO, List, Text)

def enabledText (memory: Text): Text :=
  match memory.splitOn "don't()" with
    | Cons first later => Cons first (later.map (piece => piece.splitOn "do()" |> .drop 1 |> .joinWith "do()")) |> .joinWith ""
    | Nil => memory

def main(): {IO, Fail} () :=
  let memory := IO.readAll()
  IO.print "Part 1: ${solvePart1 (parseInstructions memory)}"
  IO.print "Part 2: ${solvePart1 (parseInstructions (enabledText memory))}"
