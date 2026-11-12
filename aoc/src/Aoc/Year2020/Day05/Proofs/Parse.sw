--| The parser reads exactly the puzzle's format: if `parsePasses` reads
--| `input` as `passes`, each line of the input is its pass written out, 7
--| letters `F` or `B` then 3 letters `L` or `R`, one per bit, `B` and `R`
--| for 1.

namespace Aoc.Year2020.Day05.Proofs
import Aoc.Year2020.Day05 (..)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, Nat, Parse, Result, Text)

def PassWritten (read: List Char) (pass: Pass): Prop := pass.row.length = 7 ∧ pass.column.length = 3 ∧ read = written pass

--| A letter the parser accepts is the letter of the bit it gives.
theorem letterOf (lower: Char) (upper: Char) (char: Char) (allowed: (char == lower || char == upper) = True): letter lower upper (char == upper) = char :=
  match isUpper: char == upper with
    | True => Eq.sym (DecEq.sound isUpper)
    | False =>
      match isLower: char == lower with
        | True => Eq.sym (DecEq.sound isLower)

theorem readsHalf (lower: Char) (upper: Char): Parse.Reads (() => half lower upper) (read bit => read = [letter lower upper bit]) :=
  Parse.readsWeaken
    (Parse.readsMap (() => Parse.satisfy "'${lower}' or '${upper}'" (letter => letter == lower || letter == upper)) (char => char == upper) _ (Parse.readsSatisfy))
    (read bit h =>
      match h with
        | Witness char (Both (Both one allowed) made) => rewrite made, one, letterOf lower upper char allowed in rfl)

theorem readsPass: Parse.Reads pass PassWritten :=
  Parse.readsThen (Parse.readsExactly 7 frontBack _ (readsHalf 'F' 'B')) (rowRead row (Both rowEach rowLength) =>
    Parse.readsThen (Parse.readsExactly 3 leftRight _ (readsHalf 'L' 'R')) (columnRead column (Both columnEach columnLength) =>
      Parse.readsDone { row, column } _
        (Both (omega) (Both (omega)
          (rewrite List.appendNil columnRead,
            Parse.eachChars (letter 'F' 'B') rowRead row rowEach,
            Parse.eachChars (letter 'L' 'R') columnRead column columnEach in rfl)))))

--| Every line of the input is its pass written out.
theorem parseWritten (input: Text) (passes: List Pass) (parsed: Fail.toResult (() => parsePasses input) = Ok passes):
    List.All2 PassWritten (input.lines.map Text.toList) passes :=
  Parse.eachLineReads input pass PassWritten passes parsed readsPass
