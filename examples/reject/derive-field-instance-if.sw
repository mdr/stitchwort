-- expect-error: E-TYPE-MISMATCH
-- An `if` on an order whose instance waits for the failed `colorOrd`: the
-- condition waits too, rather than reporting a second error (SW-3078).
import Std (Ord)

type Color =
  | Red
  | Green

instance colorOrd: Ord Color := True

type Thing = { color: Color, name: Text }

def redThing: Thing := { color = Red, name = "r" }
def greenThing: Thing := { color = Green, name = "g" }

test "if" := if redThing < greenThing then True else False
