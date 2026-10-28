-- Quadrants: the program sorts each tile into a quadrant by comparing it
-- with `width / 2` and `height / 2`; the spec counts the tiles with more (or
-- fewer) tiles on one side than the other. For odd sizes they agree, the
-- middle row and column counting in no quadrant (`quadrantAgrees`), so the
-- safety factors are equal (`safetyFactorCorrect`).

namespace Aoc.Year2024.Day14.Proofs
import Aoc.Year2024.Day14 (..)
import Aoc.Year2024.Day14.Spec (..)
import Std (Bool, Eq, List, Nat, Option)

theorem topLeftAgrees (space: Space) (oddWidth: space.width % 2 = 1) (oddHeight: space.height % 2 = 1) (position: Position):
    (space.quadrantOf position == Some TopLeft) = (isTop space position && isLeft space position) :=
  cases

theorem topRightAgrees (space: Space) (oddWidth: space.width % 2 = 1) (oddHeight: space.height % 2 = 1) (position: Position):
    (space.quadrantOf position == Some TopRight) = (isTop space position && isRight space position) :=
  cases

theorem bottomLeftAgrees (space: Space) (oddWidth: space.width % 2 = 1) (oddHeight: space.height % 2 = 1) (position: Position):
    (space.quadrantOf position == Some BottomLeft) = (isBottom space position && isLeft space position) :=
  cases

theorem bottomRightAgrees (space: Space) (oddWidth: space.width % 2 = 1) (oddHeight: space.height % 2 = 1) (position: Position):
    (space.quadrantOf position == Some BottomRight) = (isBottom space position && isRight space position) :=
  cases

-- How many tiles the program puts in `quadrant` is how many the spec's two
-- tests pass.
theorem countQuadrant (space: Space) (quadrant: Quadrant) (first: Position → Bool) (second: Position → Bool)
    (agrees: (position: Position) → (space.quadrantOf position == Some quadrant) = (first position && second position))
    (positions: List Position): (positions.filterMap space.quadrantOf).count (== quadrant) = countWhere positions first second :=
  rewrite countFilterMap space.quadrantOf quadrant positions, List.lengthFilter positions (position => first position && second position)
  in List.countCongMem positions (position => space.quadrantOf position == Some quadrant) (position => first position && second position)
    (position member => agrees position)

theorem safetyFactorCorrect (space: Space) (oddWidth: space.width % 2 = 1) (oddHeight: space.height % 2 = 1) (positions: List Position):
    safetyFactor space positions = space.safetyFactor positions :=
  rewrite <- countQuadrant space TopLeft (isTop space) (isLeft space) (topLeftAgrees space oddWidth oddHeight) positions,
    <- countQuadrant space TopRight (isTop space) (isRight space) (topRightAgrees space oddWidth oddHeight) positions,
    <- countQuadrant space BottomLeft (isBottom space) (isLeft space) (bottomLeftAgrees space oddWidth oddHeight) positions,
    <- countQuadrant space BottomRight (isBottom space) (isRight space) (bottomRightAgrees space oddWidth oddHeight) positions
  in ring
