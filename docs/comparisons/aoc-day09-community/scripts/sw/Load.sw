namespace Scratch.Load
import Aoc.Year2025.Day09 (area)
import Std (IO, Text)

def main(): {IO} () :=
  let input := IO.readAll()
  IO.print "Read ${Text.length input} ${area { x = 1, y = 2 } { x = 5, y = 7 }}"
