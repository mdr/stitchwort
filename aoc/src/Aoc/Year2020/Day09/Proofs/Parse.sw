--| The parser reads exactly the puzzle's format: if `parseData` reads
--| `input`, each line of it is its number written in decimal.

namespace Aoc.Year2020.Day09.Proofs
import Aoc.Year2020.Day09 (..)
import Aoc.Year2020.Day09.Spec (NumberWritten)
import Std (Fail, List, Parse, Result, Text, Void)

theorem parseWritten ∀ (input: Text) (data: XmasData) (parsed: Fail.toResult (() => parseData input) = Ok data):
    List.All2 NumberWritten (input.lines.map Text.toList) data.numbers :=
  let ran := rewrite Fail.toResultThen (() => Parse.eachLine input Parse.nat) (numbers => ({ numbers }: XmasData)) at parsed in parsed
  match e: Fail.toResult (() => Parse.eachLine input Parse.nat) with
    | Ok numbers => rewrite <- Result.okInjective ran in Parse.eachLineReads input Parse.nat NumberWritten numbers e Parse.readsNat
