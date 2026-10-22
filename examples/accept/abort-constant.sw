-- A top-level constant (no parameters) whose body is a handler with an `if`
-- in it. Under `run --js` the `if` is a helper, `firstIsA.%match1`, which
-- the constant uses as soon as the module loads, so it must be emitted
-- before the constant (SW-299).
import Std.Abort (abort, toOption, need)
import Std (Abort, IO)

-- The first line is "a": `Some 3`; any other line, or none: `None`.
def firstIsA: {IO} Option Nat :=
  toOption (() => if (need (IO.readLine())) == "a" then 3 else abort())

def main(): {IO} () :=
  match firstIsA with
    | Some n => IO.print "a"
    | None => IO.print "not a"
