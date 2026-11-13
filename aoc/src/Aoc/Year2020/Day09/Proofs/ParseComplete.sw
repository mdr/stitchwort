--| The converse of `Parse.sw`: input whose lines are numbers written in
--| decimal is read as those numbers.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day09.Proofs
import Aoc.Year2020.Day09 (..)
import Aoc.Year2020.Day09.Spec (NumberWritten)
import Std (Eq, Fail, List, Parse, Result, Text)

theorem runsNumber (read: List Char) (number: Nat) (written: NumberWritten read number): Parse.Runs Parse.nat read [] number :=
  match written with
    | Both some (Both digits value) => rewrite value in Parse.runsNat read [] some digits rfl

theorem dataEta (data: XmasData): ({ numbers = data.numbers }: XmasData) = data := match data with
  | { numbers } => rfl

--| Input whose lines are numbers written out is read as those numbers.
theorem parseComplete (input: Text) (data: XmasData) (written: List.All2 NumberWritten (input.lines.map Text.toList) data.numbers):
    Fail.toResult (() => parseData input) = Ok data :=
  let lines: Fail.toResult (() => Parse.eachLine input Parse.nat) = Ok data.numbers :=
    Parse.runsEachLine input Parse.nat data.numbers (List.all2Weaken runsNumber _ _ written)
  rewrite Fail.toResultThen (() => Parse.eachLine input Parse.nat) (numbers => ({ numbers }: XmasData)), lines, dataEta data in rfl

--| A line is written as at most one number, because the parser reads it as one.
theorem writtenUnique (chars: List Char) (a: Nat) (b: Nat) (writtenA: NumberWritten chars a) (writtenB: NumberWritten chars b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (Parse.runsRun Parse.nat chars a (runsNumber chars a writtenA))) (Parse.runsRun Parse.nat chars b (runsNumber chars b writtenB)))

--| ... and an input is written as at most one list of numbers.
theorem inputUnique (input: Text) (a: XmasData) (b: XmasData) (writtenA: List.All2 NumberWritten (input.lines.map Text.toList) a.numbers)
    (writtenB: List.All2 NumberWritten (input.lines.map Text.toList) b.numbers): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
