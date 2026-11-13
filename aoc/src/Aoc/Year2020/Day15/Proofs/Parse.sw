--| The parser reads exactly the puzzle's format: if `parseStarting` reads
--| `input`, the input is the starting numbers written out as
--| `Spec.StartingWritten` says, then any line breaks.

namespace Aoc.Year2020.Day15.Proofs
import Aoc.Year2020.Day15 (..)
import Aoc.Year2020.Day15.Spec (NumberWritten, StartingWritten)
import Std (Fail, List, NonEmptyList, Parse, Text)

theorem readsStarting: Parse.Reads starting StartingWritten :=
  Parse.readsWeaken [p := starting] [weaker := StartingWritten]
    (Parse.readsMap (() => Parse.sepBy1 Parse.nat (() => Parse.char ',')) (numbers => { numbers }) _
      (Parse.readsSepBy1 Parse.nat (() => Parse.char ',') NumberWritten _ Parse.readsNat (Parse.readsChar ',')))
    (read value (Witness numbers (Both written same)) => rewrite same in written)

theorem parseWritten ∀ (input: Text) (starting: Starting) (parsed: Fail.toResult (() => parseStarting input) = Ok starting):
    ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ StartingWritten read starting ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  Parse.allReads input Aoc.Year2020.Day15.starting StartingWritten starting parsed readsStarting
