--| Both answers are the spec's, for every rectangle of digits: the
--| search's theorem (Search.sw) on the program's maps, whose levels are
--| the spec's (Levels.sw).
-- The maps' levels are functions, equal by `Quot.funext` since they agree
-- at every position.

namespace Aoc.Year2021.Day15.Proofs
import Aoc.Year2021.Day15 (..)
import Aoc.Year2021.Day15.Spec (..)
import Aoc.Common (Position)
import Std (DecEq, Decidable, Eq, Nat, Option, Quot, Void)

--| Part 1 is the lowest total risk through the cave.
theorem part1Correct ∀ (cave: Cave) (rectangle: Rectangle cave): Part1Answer cave (solvePart1 cave) :=
  let same := Quot.funext Position (_ => Option Nat) (levelAt cave) cave.risks.levelAt (levelsAgree cave rectangle)
  let found: LowestRisk cave.risks.levelAt (bottomRight cave.height cave.width) (solvePart1 cave) :=
    lowestRiskCorrect cave.risks (arithmetic [heightNotZero cave rectangle]) rectangle.left
  J (levels _ => LowestRisk levels (bottomRight cave.height cave.width) (solvePart1 cave)) found same.flipped

--| The full cave is five times the cave's size each way.
theorem tiledSize ∀ (cave: Cave)
    (rectangle: Rectangle cave):
    cave.tiled.height = 5 * cave.height ∧ cave.tiled.width = 5 * cave.width :=
  let wide: cave.width ≠ 0 := arithmetic [rectangle.left]
  let tall: cave.height ≠ 0 := heightNotZero cave rectangle
  rewrite tiledIsTiles cave tall wide then Both byComputing byComputing

--| Part 2 is the lowest total risk through the full cave.
theorem part2Correct ∀ (cave: Cave) (rectangle: Rectangle cave): Part2Answer cave (solvePart2 cave) :=
  let same :=
    Quot.funext Position (_ => Option Nat) (tiledLevelAt cave) cave.tiled.levelAt (tiledLevelsAgree cave rectangle)
  -- Projections rather than a `let (Both …)`, whose match would read the
  -- goal back, and with it the search the answer unfolds to.
  let height := (tiledSize cave rectangle).left
  let width := (tiledSize cave rectangle).right
  let tall := heightNotZero cave rectangle
  let found := lowestRiskCorrect cave.tiled (arithmetic [height, tall]) (arithmetic [width, rectangle.left])
  let target := bottomRight (5 * cave.height) (5 * cave.width)
  let sameTarget: bottomRight cave.tiled.height cave.tiled.width = target :=
    Eq.trans
      (Eq.cong (h => bottomRight h cave.tiled.width) height)
      (Eq.cong (w => bottomRight (5 * cave.height) w) width)
  let resized: LowestRisk cave.tiled.levelAt target (solvePart2 cave) :=
    J (corner _ => LowestRisk cave.tiled.levelAt corner (solvePart2 cave)) found sameTarget
  J (levels _ => LowestRisk levels target (solvePart2 cave)) resized same.flipped
