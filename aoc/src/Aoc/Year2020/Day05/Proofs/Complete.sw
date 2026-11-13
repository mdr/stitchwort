--| The converse of `Parse.sw`: every line written out as seven `F`/`B` letters
--| and three `L`/`R` letters is read as its pass, and so is a whole input of
--| such lines.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day05.Proofs
import Aoc.Year2020.Day05 (..)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, Nat, Parse, Result, Text)

theorem passEta ∀ (pass: Pass): { row = pass.row, column = pass.column } = pass := match pass with
  | { row, column } => rfl

theorem runsAs ∀ (chars: List Char) (a: Pass) (b: Pass) (same: a = b) (runs: Parse.Runs pass chars [] a): Parse.Runs pass chars [] b :=
  rewrite same at runs in runs

--| `half` reads the letter of the bit it gives.
theorem runsHalf ∀ (lower: Char) (upper: Char) (differ: (upper == lower) = False) (bit: Bool) (rest: List Char):
    Parse.Runs (() => half lower upper) [letter lower upper bit] rest bit := match bit with
      | True =>
        let runs := Parse.runsMap (() => Parse.satisfy "'${lower}' or '${upper}'" (char => char == lower || char == upper)) (char => char == upper) [upper] rest upper
          (Parse.runsSatisfy _ _ upper rest (Bool.orRight (DecEq.refl upper)))
        rewrite DecEq.refl upper at runs in runs
      | False =>
        let lowerNotUpper: (lower == upper) = False := Eq.trans (DecEq.eqComm lower upper) differ
        let runs := Parse.runsMap (() => Parse.satisfy "'${lower}' or '${upper}'" (char => char == lower || char == upper)) (char => char == upper) [lower] rest lower
          (Parse.runsSatisfy _ _ lower rest (Bool.orLeft (DecEq.refl lower)))
        rewrite lowerNotUpper at runs in runs

theorem runsPass ∀ (chars: List Char) (seat: Pass) (written: PassWritten chars seat): Parse.Runs pass chars [] seat :=
  match written with
    | Both rowLength (Both columnLength same) =>
      let rowRuns := Parse.runsExactlySymbols 7 frontBack (letter 'F' 'B') (bit after => runsHalf 'F' 'B' rfl bit after) seat.row
      let columnRuns := Parse.runsExactlySymbols 3 leftRight (letter 'L' 'R') (bit after => runsHalf 'L' 'R' rfl bit after) seat.column
      rewrite same in
        runsAs _ _ seat (passEta seat)
          (Parse.runsBind (() => Parse.exactly 7 frontBack) _ (seat.row.map (letter 'F' 'B')) (seat.column.map (letter 'L' 'R')) _ [] seat.row _ rfl
            (rowRuns _ rowLength)
            (Parse.runsBind (() => Parse.exactly 3 leftRight) _ (seat.column.map (letter 'L' 'R')) [] _ [] seat.column _ (Eq.sym (List.appendNil _))
              (columnRuns [] columnLength)
              (Parse.runsPure _ [])))

--| Input whose lines are passes written out is read as those passes.
theorem parseComplete ∀ (input: Text) (passes: List Pass) (written: List.All2 PassWritten (input.lines.map Text.toList) passes):
    Fail.toResult (() => parsePasses input) = Ok passes :=
  Parse.runsEachLine input pass passes (List.all2Weaken runsPass _ _ written)

--| A line is written as at most one pass, because the parser reads it as one
--| and that read is a function of the line.
theorem writtenUnique ∀ (chars: List Char) (a: Pass) (b: Pass) (writtenA: PassWritten chars a) (writtenB: PassWritten chars b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (Parse.runsRun pass chars a (runsPass chars a writtenA))) (Parse.runsRun pass chars b (runsPass chars b writtenB)))

--| ... and an input is written as at most one list of passes.
theorem inputUnique ∀ (input: Text) (a: List Pass) (b: List Pass) (writtenA: List.All2 PassWritten (input.lines.map Text.toList) a)
    (writtenB: List.All2 PassWritten (input.lines.map Text.toList) b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
