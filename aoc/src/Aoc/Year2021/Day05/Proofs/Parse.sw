--| The parser keeps the puzzle's promise: every line of a successful
--| parse is horizontal, vertical or diagonal at 45 degrees, so part 2's
--| theorem holds of whatever `parseLines` reads.
-- (D2108)

namespace Aoc.Year2021.Day05.Proofs
import Aoc.Common (..)
import Aoc.Year2021.Day05 (..)
import Aoc.Year2021.Day05.Spec (..)
import Std (Bool, Eq, Fail, List, Option, Result, Void)

--| Part 2 from the input text: if `parseLines` reads `input` as `lines`,
--| part 2's answer is the number of points where at least two of them
--| overlap.
theorem part2FromInput ∀ (input: Text) (lines: List Line) (parsed: Fail.toResult (() => parseLines input) = Ok lines):
    Part2Answer lines (solvePart2 lines) :=
  part2Correct lines (parseLinesShapes input lines parsed)

--| Every line `parseLines` reads is horizontal, vertical or diagonal.
theorem parseLinesShapes ∀ (input: Text) (lines: List Line) (parsed: Fail.toResult (() => parseLines input) = Ok lines):
    lines.all (line => horizontalOrVertical line ∨ diagonal line) = True :=
  checkedShapes _ lines parsed

--| Whatever reads the lines, `checkShapes` passes on only lines of the
--| shapes the puzzle allows.
theorem checkedShapes ∀ (read: () → {Fail} List Line) (lines: List Line) (parsed: Fail.toResult (() => checkShapes (read ())) = Ok lines):
    lines.all (line => horizontalOrVertical line ∨ diagonal line) = True :=
  let split := rewrite Fail.toResultThen read checkShapes at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkShapes x)) lines split
    (u _ checked => checkShapesOk u lines checked)

--| `checkShapes` passes its lines on unchanged, and only if every one has a
--| shape the puzzle allows.
theorem checkShapesOk ∀ (lines: List Line) (checked: List Line) (h: Fail.toResult (() => checkShapes lines) = Ok checked):
    checked.all (line => horizontalOrVertical line ∨ diagonal line) = True := match e: firstBent lines with
      | Some (index, _) => Void.exfalso (Result.errNotOk h)
      | None =>
        rewrite <- Result.okInjective h in
          List.findNotNoneAll lines (line => line.isStraight ∨ line.isDiagonal)
            (List.findWithIndexFromNone (line => not (line.isStraight ∨ line.isDiagonal)) 0 lines e)
