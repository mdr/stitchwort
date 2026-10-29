-- Parse the input with the committed parser and print its size, no solving.
namespace Scratch.ParseOnly
import Aoc.Year2024.Day05 (..)
import Std (Fail, IO, List, Text)

def main(): {IO, Fail} () :=
  let queue := parsePrintQueue IO.readAll()
  IO.print "Read ${queue.rules.length} rules and ${queue.updates.length} updates"
