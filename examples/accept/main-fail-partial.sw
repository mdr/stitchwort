-- A partial `main` that may fail (docs/proposals/partial-stage-2.md): a
-- loop that reads numbers until the end of its input, with no bound, and
-- fails on a line that isn't one. `stitchwort run` performs the failure
-- itself: it prints `error: <message>` on standard error and exits with 1.
-- What was printed before the failure stays printed. (run: fails)
import Std (IO, Fail, Text)

def sumLines (total: Nat): {IO, Fail, Partial} Nat :=
  match IO.readLine() with
    | None => total
    | Some line =>
      let number := Text.toNatOrFail line
      IO.print "total so far ${total + number}"
      sumLines (total + number)

def main(): {IO, Fail, Partial} () := IO.print "sum ${sumLines 0}"
