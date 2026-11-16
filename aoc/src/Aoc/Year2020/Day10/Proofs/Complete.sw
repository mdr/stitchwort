--| The converse of `Parse.sw`: input whose lines are adapters written in
--| decimal is read as those adapters.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day10.Proofs
import Aoc.Year2020.Day10 (..)
import Aoc.Year2020.Day10.Spec (RatingWritten)
import Std (Eq, Fail, List, Parse, Result, Text)

theorem runsRating ∀ (read: List Char) (number: Nat)
    (written: RatingWritten read number):
    Parse.Runs Parse.nat read [] number :=
  match written with | Both some (Both digits value) => rewrite value then Parse.runsNat read [] some digits byComputing

theorem bagEta ∀ (bag: Bag): ({ adapters = bag.adapters }: Bag) = bag := match bag with | { adapters } => byComputing

--| Input whose lines are adapters written out is read as those adapters.
theorem parseComplete ∀ (input: Text) (bag: Bag)
    (written: List.All2 RatingWritten (input.lines.map Text.toList) bag.adapters):
    Fail.toResult (() => parseBag input) = Ok bag :=
  let lines: Fail.toResult (() => Parse.eachLine input Parse.nat) = Ok bag.adapters :=
    Parse.runsEachLine input Parse.nat bag.adapters (List.all2Weaken runsRating _ _ written)
  rewrite Fail.toResultThen (() => Parse.eachLine input Parse.nat) (adapters => ({ adapters }: Bag)),
      lines,
      bagEta bag then
    byComputing

--| A line is written as at most one rating, because the parser reads it as one.
theorem writtenUnique ∀ (chars: List Char) (a b: Nat)
    (writtenA: RatingWritten chars a)
    (writtenB: RatingWritten chars b):
    a = b :=
  Result.okInjective
    (Eq.trans
      (Eq.flipped (Parse.runsRun Parse.nat chars a (runsRating chars a writtenA)))
      (Parse.runsRun Parse.nat chars b (runsRating chars b writtenB)))

--| ... and an input is written as at most one list of adapters.
theorem inputUnique ∀ (input: Text) (a b: Bag)
    (writtenA: List.All2 RatingWritten (input.lines.map Text.toList) a.adapters)
    (writtenB: List.All2 RatingWritten (input.lines.map Text.toList) b.adapters):
    a = b :=
  Result.okInjective (Eq.trans (parseComplete input a writtenA).flipped (parseComplete input b writtenB))
