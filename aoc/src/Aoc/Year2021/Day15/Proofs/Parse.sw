-- The parser keeps the puzzle's promise (D2108): what `parseCave` reads is
-- a rectangle of digits with at least one, the `Rectangle` the answers'
-- theorems assume. So the answers are the spec's for every input the
-- parser accepts, with no hypothesis (`part1FromInput`, `part2FromInput`).
-- Levels are digits by their type (`Fin 10`). The puzzle's levels are 1 to
-- 9, but 0 needn't be excluded: a 0 is a path step that costs nothing, and
-- the tiling's wrap is right for it too (`iterateRaise` needs only a level
-- of at most 9).

namespace Aoc.Year2021.Day15.Proofs
import Aoc.Year2021.Day15 (..)
import Aoc.Year2021.Day15.Spec (..)
import Std (Bool, DecEq, Decidable, Eq, Fail, Fin, List, Nat, Result, Void)

-- What `parseCave` reads is a rectangle with a digit.
theorem parseRectangle (input: Text) (cave: Cave) (parsed: Fail.toResult (() => parseCave input) = Ok cave): Rectangle cave :=
  checkedRectangle _ cave parsed

-- Whatever reads the rows, `checkCave` passes on only a rectangle with a
-- digit.
theorem checkedRectangle (read: () → {Fail} (List (List (Fin 10)))) (cave: Cave) (parsed: Fail.toResult (() => checkCave (read ())) = Ok cave):
    Rectangle cave :=
  let split := rewrite Fail.toResultThen read checkCave at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkCave x)) cave split (rows _ checked => checkCaveOk rows cave checked)

-- `checkCave` keeps its rows, and only if the first has a digit and each
-- is as long as the first.
theorem checkCaveOk (rows: List (List (Fin 10))) (cave: Cave) (h: Fail.toResult (() => checkCave rows) = Ok cave): Rectangle cave :=
  match empty: width rows == 0 with
    | True => Void.exfalso (Result.errNotOk _ cave h)
    | False =>
      match e: firstRagged rows with
        | Some (index, _) => Void.exfalso (Result.errNotOk _ cave h)
        | None =>
          let same: rows = cave.rows := Eq.cong Cave.rows (Result.okInjective _ cave h)
          let notRagged := List.findNoneAll rows (row => row.length != width rows) (List.findWithIndexFromNone (row => row.length != width rows) 0 rows e)
          let wide: Not (width rows = 0) := Decidable.toBoolFalse _ empty
          rewrite <- same in
            Both (omega [wide])
              (row member => DecEq.neFalse row.length (width rows) (Bool.notTrue _ (List.allMem _ row rows (List.allToAll _ rows notRagged) member)))

-- Part 1's answer is the lowest total risk, for every input the parser
-- accepts.
theorem part1FromInput (input: Text) (cave: Cave) (parsed: Fail.toResult (() => parseCave input) = Ok cave): Part1Answer cave (solvePart1 cave) :=
  part1Correct cave (parseRectangle input cave parsed)

-- Part 2's answer is the lowest total risk through the full cave, for
-- every input the parser accepts.
theorem part2FromInput (input: Text) (cave: Cave) (parsed: Fail.toResult (() => parseCave input) = Ok cave): Part2Answer cave (solvePart2 cave) :=
  part2Correct cave (parseRectangle input cave parsed)
