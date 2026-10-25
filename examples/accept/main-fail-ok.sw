-- A `main` that may fail but doesn't: it runs as any other, and exits with 0.
import Std (IO, Fail, List, Text)

def main(): {IO, Fail} () :=
  IO.print "reading the numbers"
  let total := List.sum (List.map ["1", " 2 ", "3"] Text.toNatOrFail)
  IO.print "total ${total}"
