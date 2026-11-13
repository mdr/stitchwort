--| The parser keeps the puzzle's promises: every height is a digit, 0 to 9, by
--| its type (`Fin 10`; `heightBelow10` in Facts.sw), and every row of a
--| successful parse is as long as the first, so the map is a rectangle (the
--| shared grid parser's `parseGridRectangle`). Neither theorem of the answers
--| needs either: they hold for every map, rectangular or not.
-- (D2108)

namespace Aoc.Year2021.Day09.Proofs
import Aoc.Year2021.Day09 (..)
import Aoc.Common (parseGrid)
import Aoc.Common.Proofs (parseGridRectangle)
import Std (Eq, Fail, Fin, List, Result)
import Std.Parse (digit)

--| Every row `parseHeightMap` reads is as long as the first.
theorem parseRectangular ∀ (input: Text) (map: HeightMap) (parsed: Fail.toResult (() => parseHeightMap input) = Ok map) (row: List (Fin 10))
    (member: row ∈ map.grid.rows): row.length = map.grid.width :=
  let split := rewrite Fail.toResultThen (() => parseGrid input digit) (grid => ({ grid }: HeightMap)) at parsed
  Result.flatMapEqOk (Fail.toResult (() => parseGrid input digit)) (grid => Fail.toResult (() => ({ grid }: HeightMap))) map split
    (grid read made =>
      let same: ({ grid }: HeightMap) = map := Result.okInjective made
      let rectangle := And.left (parseGridRectangle input digit grid read)
      rewrite <- same in rectangle row (rewrite <- same at member in member))
