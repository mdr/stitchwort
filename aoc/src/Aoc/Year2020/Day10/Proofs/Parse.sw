--| The parser reads exactly the puzzle's format: if `parseBag` reads
--| `input`, each line of it is its rating written in decimal.

namespace Aoc.Year2020.Day10.Proofs
import Aoc.Year2020.Day10 (..)
import Aoc.Year2020.Day10.Spec (RatingWritten)
import Std (Fail, List, Parse, Result, Text, Void)

theorem parseWritten (input: Text) (bag: Bag) (parsed: Fail.toResult (() => parseBag input) = Ok bag):
    List.All2 RatingWritten (input.lines.map Text.toList) bag.adapters :=
  let ran := rewrite Fail.toResultThen (() => Parse.eachLine input Parse.nat) (adapters => ({ adapters }: Bag)) at parsed in parsed
  match e: Fail.toResult (() => Parse.eachLine input Parse.nat) with
    | Ok adapters => rewrite <- Result.okInjective ran in Parse.eachLineReads input Parse.nat RatingWritten adapters e Parse.readsNat
