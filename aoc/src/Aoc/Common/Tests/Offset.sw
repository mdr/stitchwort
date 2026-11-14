--| Tests for offsets.
-- Kept apart from the code, so that running a day doesn't check them.

namespace Aoc.Common.Tests
import Aoc.Common (..)
import Std (Int, List, Option)

def by (rows columns: Int): Offset := { rows, columns }

test "minus" := (at 1 5).minus (at 3 2) == by (-2) 3 ∧ (at 3 2).minus (at 3 2) == Offset.zero
test "offset" :=
  (at 3 2).offset (by (-2) 3) == Some (at 1 5)
    ∧ (at 3 2).offset (by (-4) 0) == None
    ∧ (at 3 2).offset (by 0 (-3)) == None
test "offset by the step from one to another" := (at 3 2).offset ((at 0 7).minus (at 3 2)) == Some (at 0 7)
test "plus, negate and times" :=
  (by 1 (-2)).plus (by 3 4) == by 4 2 ∧ (by 1 (-2)).negate == by (-1) 2 ∧ (by 1 (-2)).times (-3) == by (-3) 6
test "a direction's offset is its step" := directions.all (direction =>
  (at 0 0).step direction == (at 0 0).offset direction.offset
    ∧ (at 2 2).step direction == (at 2 2).offset direction.offset)
test "a grid's offset" :=
  small.offset (at 0 0) (by 1 2) == Some (at 1 2)
    ∧ small.offset (at 0 0) (by 2 0) == None
    ∧ small.offset (at 0 0) (by 0 3) == None
test "wrap" :=
  (at 0 0).wrap (by (-1) (-1)) 7 11 == at 6 10
    ∧ (at 2 3).wrap (by 15 (-25)) 7 11 == at 3 0
    ∧ (at 4 2).wrap (by (-7) 11) 7 11 == at 4 2
test "wrapping twice is wrapping by the sum" :=
  (at 1 1).wrap (by 5 (-4)) 7 11 |> .wrap (by 3 9) 7 11 |> (== (at 1 1).wrap (by 8 5) 7 11)
