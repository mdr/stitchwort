-- expect-error: E-TYPE-MISMATCH
-- `Outer`'s derived `Ord` reaches `Thing`'s, which waits for the failed
-- `colorOrd`: the use waits too, rather than reporting a second error
-- (SW-3078).
import Std (Ord)

type Color =
  | Red
  | Green

instance colorOrd: Ord Color := True

type Thing = { color: Color, name: Text }

type Outer = { thing: Thing }

def redOuter: Outer := { thing = { color = Red, name = "r" } }
def greenOuter: Outer := { thing = { color = Green, name = "g" } }

test "ordered" := Ord.compare redOuter greenOuter == Less
