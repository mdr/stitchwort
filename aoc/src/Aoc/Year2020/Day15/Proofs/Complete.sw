--| The converse of `Parse.sw`: starting numbers written out, separated by
--| commas, then any line breaks, are read as those numbers.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day15.Proofs
import Aoc.Year2020.Day15 (..)
import Aoc.Year2020.Day15.Spec (NumberWritten, StartingWritten)
import Std (Bool, Char, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Text, Void)

theorem runsNumber (read: List Char) (number: Nat) (after: List Char) (written: NumberWritten read number) (stops: Parse.CannotStart Parse.isDigit after):
    Parse.Runs Parse.nat read after number := match written with
      | Both nonEmpty (Both allDigits decimal) =>
        rewrite decimal in Parse.runsNatBefore read after nonEmpty allDigits stops

theorem runsStarting (read: List Char) (starting2: Starting) (written: StartingWritten read starting2) (ending: List Char) (breaks: Parse.OnlyBreaks ending):
    Parse.Runs starting read ending starting2 := match starting2, written with
      | { numbers }, written2 =>
        match numbers, written2 with
          | { head, tail }, written3 =>
        Parse.runsMap (() => Parse.sepBy1 Parse.nat (() => Parse.char ',')) (numbers2 => { numbers = numbers2 }) read ending (NonEmptyList.cons head tail)
          (Parse.runsSepBy1Of Parse.nat (() => Parse.char ',') NumberWritten (read2 u => read2 = [',']) (Parse.CannotStart Parse.isDigit) ending
            (read2 v after ok stops => runsNumber read2 v after ok stops)
            (read2 after u same => rewrite same in Parse.runsChar ',' after)
            (read2 u same => rewrite same in List.consNotNil ',' [])
            (read2 after u same => rewrite same in (char more found => rewrite <- List.consInjectiveHead _ _ _ _ found in rfl))
            (Parse.cannotStartAtBreaks Parse.isDigit rfl rfl ending breaks)
            (Parse.declinesSepStep Parse.nat (() => Parse.char ',') ending (Parse.declinesCharCannotStart ',' (char => char == ',') rfl ending (Parse.cannotStartAtBreaks (char => char == ',') rfl rfl ending breaks)))
            read head tail written3)

--| The soundness theorem's conclusion: the input is the numbers written out,
--| then any line breaks.
def InputWritten (input: Text) (starting2: Starting): Prop :=
  ∃ (read: List Char) => ∃ (ending: List Char) =>
    input.toList = read ++ ending ∧ StartingWritten read starting2 ∧ ending.all (char => char == '\n' ∨ char == '\r') = True

--| Input that is starting numbers written out is read as those numbers.
theorem parseComplete (input: Text) (starting2: Starting) (written: InputWritten input starting2): Fail.toResult (() => parseStarting input) = Ok starting2 :=
  match written with
    | Witness read (Witness ending (Both split (Both startingWritten breaks))) =>
      Parse.runsAll input starting read ending starting2 split breaks (runsStarting read starting2 startingWritten ending breaks)

--| Soundness (`parseWritten`) is the converse: the input is written as at most one starting list.
theorem writtenUnique (input: Text) (a: Starting) (b: Starting) (writtenA: InputWritten input a) (writtenB: InputWritten input b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
