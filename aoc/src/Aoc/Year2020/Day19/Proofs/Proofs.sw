--| Day 19 proved: when `Rules.productive` holds (the rules are ranked by
--| `Rules.rank`, below `Rules.rankBound`), `matchesCompletely` is true of a
--| message exactly when the message completely matches rule 0 in the
--| puzzle's sense (Sound.sw, Complete.sw), so the program's count is the
--| spec's answer and the only one, in both parts. Parse.sw has that the
--| parser reads the puzzle's format.

namespace Aoc.Year2020.Day19.Proofs
import Aoc.Year2020.Day19 (..)
import Aoc.Year2020.Day19.Spec (..)
import Aoc.Year2020.Day19 (Spec)
import Std (Bool, Char, DecEq, Eq, Exists, List, Nat, Option, Void)

-- The ranks

theorem chainBounded (rules: Rules) (fuel number: Nat): rules.chain fuel number ≤ fuel :=
  match fuel with
    | Zero => omega
    | Succ more =>
      match looked: rules.rule number with
        | Some (Alternatives sequences) =>
          match found: sequences.map (rules.chainThrough more) |> .maximum with
            | None => omega
            | Some most =>
              match List.memMapElim (rules.chainThrough more) most sequences (And.left (List.maximumSome _ most found)) with
                | Witness sequence (Both chosen made) =>
                  rewrite <- made in
                    match sequence with
                      | [] => omega
                      | [only] => omega [chainBounded rules more only]
                      | [first, second, ..others] => omega
        | Some (Letter letter) => omega
        | None => omega

theorem rankBelow (rules: Rules) (number: Nat): rules.rank number < rules.rankBound :=
  omega [chainBounded rules (rules.numbered.length + 1) number]

theorem lookupMember (entries: List (Nat, Rule)) (number: Nat) (rule: Rule) (found: entries.lookup number = Some rule): (number, rule) ∈ entries :=
  match entries with
    | [(entryNumber, value), ..rest] =>
      match same: entryNumber == number with
        | True => Inl (rewrite same.read, Option.someInjective found in rfl)
        | False => Inr (lookupMember rest number rule found)

theorem productiveRanked (rules: Rules) (rank: Nat → Nat) (bound: Nat) (below: ∀ (number: Nat) => rank number < bound)
    (productive: rules.productiveWith rank = True): Ranked rules rank bound :=
  Both below (number sequences looked sequence chosen =>
    let entryProductive := productive.read (number, Alternatives sequences) (lookupMember rules.numbered number (Alternatives sequences) looked)
    let sequenceProductive := entryProductive.read sequence chosen
    match sequence with
      | [single] => Both (List.consNotNil single []) (only same => rewrite <- List.consInjectiveHead single only [] [] same in omega [sequenceProductive])
      | [first, second, ..others] => Both (List.consNotNil first [second, ..others]) (only same => Void.exfalso (List.consNotNil second others (Eq.cong (.drop 1) same))))

-- Deciding a message

theorem anyEmpty (lefts: List (List Char)) (any: lefts.any .isEmpty = True): [] ∈ lefts :=
  let Witness left (Both member empty) := any
  match left with
    | [] => member

--| `matchesCompletely` reads the rules from a table, but the list gives its answer.
theorem matchesCompletelyList (rules: Rules) (message: Message):
    rules.matchesCompletely message = (rules.leftAfter (rules.enough message) 0 message.letters |> .any .isEmpty) :=
  rewrite leftAfterSame (ruleTable rules.numbered).get rules.rule (tableRule rules) (rules.enough message) 0 message.letters in rfl

theorem matchesCompletelyCorrect (rules: Rules) (productive: rules.productive = True) (message: Message):
    rules.matchesCompletely message = True ↔ MatchesCompletely rules message :=
  let ranked := productiveRanked rules rules.rank rules.rankBound (rankBelow rules) productive
  rewrite matchesCompletelyList rules message in {
    forward = matches =>
      match sound rules (rules.enough message) 0 message.letters [] (anyEmpty _ matches) with
        | Witness read (Both split leads) => rewrite split in leads [] [] MatchesNothing,
    backward = matched =>
      let enough: message.letters.length * rules.rankBound + rules.rank 0 < rules.enough message :=
        let same: (message.letters.length + 1) * rules.rankBound = message.letters.length * rules.rankBound + rules.rankBound := ring
        omega [same, rankBelow rules 0]
      let found := completeAll rules rules.rank rules.rankBound ranked [0] message.letters matched (rules.enough message) enough []
      match (List.memFlatMap (left => rules.leftAfterAll (rules.enough message) [] left) [] (rules.leftAfter (rules.enough message) 0 (message.letters ++ []))).forward found with
        | Witness middle (Both first (Inl empty)) => rewrite empty, List.appendNil message.letters at first in Witness [] (Both first rfl)
        | Witness middle (Both first (Inr never)) => Void.exfalso never
  }

theorem part1Exactly (received: Received) (productive: received.rules.productive = True) (answer: Nat):
    Spec.Part1 received answer ↔ answer = received.matchingCount :=
  List.countWithIff received.rules.matchesCompletely (matchesCompletelyCorrect received.rules productive) received.messages answer

theorem part2Exactly (received: Received) (productive: received.withLoops.rules.productive = True) (answer: Nat):
    Spec.Part2 received answer ↔ answer = received.withLoops.matchingCount :=
  List.countWithIff received.withLoops.rules.matchesCompletely (matchesCompletelyCorrect received.withLoops.rules productive) received.messages answer
