-- expect-error: E-TYPE-MISMATCH
-- `colorOrd` has a type error, so `Thing`'s derived `Ord` can't be built: it
-- waits for `colorOrd` rather than reporting a second error where `Thing`'s
-- order is wanted (SW-3078).
import Std (Ord)

type Color =
  | Red
  | Green

instance colorOrd: Ord Color := True

type Thing = { color: Color, name: Text }

def redThing: Thing := { color = Red, name = "r" }
def greenThing: Thing := { color = Green, name = "g" }

test "ordered" := Ord.compare redThing greenThing == Less
