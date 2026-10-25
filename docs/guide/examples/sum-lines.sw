-- Chapter 8: a `main` that is both `Fail` and `Partial`. Run it with
--   stitchwort run sum-lines.sw < sum-lines.input
import Std (IO, Fail, Text)

def sumLines (total: Nat): {IO, Fail, Partial} Nat :=
  match IO.readLine() with
    | None => total
    | Some line =>
      let number := line.toNatOrFail
      IO.print "total so far ${total + number}"
      sumLines (total + number)

def main(): {IO, Fail, Partial} () := IO.print "sum ${sumLines 0}"
