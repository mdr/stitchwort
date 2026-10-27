-- `main` may leave `Fail` unhandled: `stitchwort run` prints `error: <message>`
-- on standard error and exits with 1. What was printed before the failure
-- stays printed. (run: fails)
import Std (IO, Fail, List, Text)

def main(): {IO, Fail} () :=
  IO.print "reading the numbers"
  let total := ["1", " 2 ", "x3"].map Text.toNatOrFail |> .sum
  IO.print "total ${total}"
