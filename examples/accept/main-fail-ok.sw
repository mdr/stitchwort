-- A `main` that may fail but doesn't: it runs as any other, and exits with 0.
import Std (IO, Fail, List, Text)

def main(): {IO, Fail} () :=
  IO.print "reading the numbers"
  let total := ["1", " 2 ", "3"].map Text.toNatOrFail |> .sum
  IO.print "total ${total}"
