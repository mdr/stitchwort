--| The parser reads exactly the puzzle's format: if `parseSlice` reads
--| `input`, each line of it is its row of the slice, a character a cube,
--| nothing dropped, added or changed; and the slice is a rectangle.

namespace Aoc.Year2020.Day17.Proofs
import Aoc.Common (Grid, checkGrid, parseGrid)
import Aoc.Common.Proofs (checkGridRows, parseGridRectangle)
import Aoc.Year2020.Day17 (..)
import Aoc.Year2020.Day17.Spec (RowWritten, symbol)
import Std (Fail, List, NonEmptyList, Parse, Result, Text)

theorem readsCubeState: Parse.Reads cubeState (read state => read = [symbol state]) :=
  Parse.readsWeaken (Parse.readsPickBy [Active, Inactive] CubeState.symbol) (read state (Both member same) =>
    match state with
      | Active => same
      | Inactive => same)

--| Every line a grid of cubes is read from is its row written out.
theorem gridWritten ∀ (input: Text) (grid: Grid CubeState)
    (parsed: Fail.toResult (() => parseGrid input cubeState) = Ok grid):
    List.All2 RowWritten (input.lines.map Text.toList) grid.rows :=
  let split :=
    rewrite Fail.toResultThen (() => Parse.eachLine input (() => Parse.many1 cubeState |> .toList)) checkGrid at parsed
  Result.flatMapEqOk _ (rows => Fail.toResult (() => checkGrid rows)) grid split (rows read checked =>
    rewrite <- checkGridRows rows grid checked in
      Parse.eachLineReads input
        (() => Parse.many1 cubeState |> .toList) _
        rows
        read
        (Parse.readsWeaken
          (Parse.readsMap
            (() => Parse.many1 cubeState)
            NonEmptyList.toList _
            (Parse.readsMany1 cubeState _ readsCubeState))
          (line values h =>
            match h with
              | Witness states (Both each same) => rewrite same in Parse.eachChars symbol line states.toList each)))

--| Every line of the input is its row of the slice written out, and the
--| slice is a rectangle.
theorem parseWritten ∀ (input: Text) (slice: Slice)
    (parsed: Fail.toResult (() => parseSlice input) = Ok slice):
    List.All2 RowWritten (input.lines.map Text.toList) slice.grid.rows ∧ slice.grid.Rectangle :=
  let split := rewrite Fail.toResultThen (() => parseGrid input cubeState) (grid => ({ grid }: Slice)) at parsed
  Result.flatMapEqOk
    (Fail.toResult (() => parseGrid input cubeState))
    (grid => Fail.toResult (() => ({ grid }: Slice)))
    slice
    split
    (grid read made =>
      let same: ({ grid }: Slice) = slice := Result.okInjective made
      rewrite <- same in Both (gridWritten input grid read) (And.left (parseGridRectangle input cubeState grid read)))
