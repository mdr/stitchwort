--| The spec's game, run directly, on the puzzle's example: it looks back
--| over every number spoken, so it is quadratic in the turns.

namespace Aoc.Year2020.Day15.Tests
import Aoc.Year2020.Day15 (..)
import Aoc.Year2020.Day15 (Spec)
import Std (List, Result)

test "the spec's first ten turns of the example" := Spec.spoken [0, 3, 6] 10 == [0, 4, 0, 1, 3, 3, 0, 6, 3, 0]
test "the spec, the example's 2020th number" := Spec.numberSpoken [0, 3, 6] 2020 == 436
test "the spec agrees with the game for 300 turns" :=
  (parsed "15,12,0,14,3,1").map (starting =>
    (0 ..= 300).all (turn => starting.numberSpoken turn == Spec.numberSpoken starting.numbers.toList turn))
    == Ok True
