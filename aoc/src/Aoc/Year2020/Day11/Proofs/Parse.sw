--| The parser reads exactly the puzzle's format: if `parseLayout` reads
--| `input`, each line of it is its row of the layout, a character a
--| position, nothing dropped, added or changed; and the layout is a
--| rectangle.

namespace Aoc.Year2020.Day11.Proofs
import Aoc.Common (Grid, checkGrid, parseGrid)
import Aoc.Common.Proofs (checkGridRows, parseGridRectangle)
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11.Spec (RowWritten, symbol)
import Std (Fail, List, NonEmptyList, Parse, Result, Text)

theorem readsSeat: Parse.Reads seat (read seat => read = [symbol seat]) :=
  Parse.readsWeaken (Parse.readsPickBy [Floor, Empty, Occupied] Seat.symbol)
    (read seat (Both member same) =>
      match seat with
        | Floor => same
        | Empty => same
        | Occupied => same)

--| Every line a grid of seats is read from is its row written out.
theorem gridWritten ∀ (input: Text) (grid: Grid Seat) (parsed: Fail.toResult (() => parseGrid input seat) = Ok grid):
    List.All2 RowWritten (input.lines.map Text.toList) grid.rows :=
  let split := rewrite Fail.toResultThen (() => Parse.eachLine input (() => Parse.many1 seat |> .toList)) checkGrid at parsed
  Result.flatMapEqOk _ (rows => Fail.toResult (() => checkGrid rows)) grid split (rows read checked =>
    rewrite <- checkGridRows rows grid checked in
      Parse.eachLineReads input (() => Parse.many1 seat |> .toList) _ rows read
        (Parse.readsWeaken
          (Parse.readsMap (() => Parse.many1 seat) NonEmptyList.toList _ (Parse.readsMany1 seat _ readsSeat))
          (line values h =>
            match h with
              | Witness seats (Both each same) => rewrite same in Parse.eachChars symbol line seats.toList each)))

--| Every line of the input is its row of the layout written out, and the
--| layout is a rectangle.
theorem parseWritten ∀ (input: Text) (layout: Layout) (parsed: Fail.toResult (() => parseLayout input) = Ok layout):
    List.All2 RowWritten (input.lines.map Text.toList) layout.grid.rows ∧ layout.grid.Rectangle :=
  let split := rewrite Fail.toResultThen (() => parseGrid input seat) (grid => ({ grid }: Layout)) at parsed
  Result.flatMapEqOk (Fail.toResult (() => parseGrid input seat)) (grid => Fail.toResult (() => ({ grid }: Layout))) layout split
    (grid read made =>
      let same: ({ grid }: Layout) = layout := Result.okInjective made
      rewrite <- same in Both (gridWritten input grid read) (And.left (parseGridRectangle input seat grid read)))
