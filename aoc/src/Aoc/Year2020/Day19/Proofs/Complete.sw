--| The matcher is complete, given enough fuel, for rules that are ranked:
--| every match of a sequence of rules is found by `leftAfterAll`, with
--| what follows the match left over. Each rule within a rule costs a fuel;
--| it either reads a letter more than the rule around it, or is an
--| alternative of one rule and has a lower rank, so a match of `read`
--| needs about `read.length * bound` fuel (`Fuelled`).

namespace Aoc.Year2020.Day19.Proofs
import Aoc.Year2020.Day19 (..)
import Aoc.Year2020.Day19.Spec (..)
import Std (Char, DecEq, Eq, Exists, List, Nat, Option, Void)

--| Every rank is below `bound`, a rule's alternatives aren't empty, and an
--| alternative of one rule leads to a rule of lower rank.
def Ranked (rules: Rules) (rank: Nat → Nat) (bound: Nat): Prop :=
  (∀ (number: Nat) => rank number < bound)
    ∧ (∀ (number: Nat) (sequences: List (List Nat)) => ruleNumbered rules number = Some (Alternatives sequences) → ∀ (sequence: List Nat) =>
      sequence ∈ sequences → sequence ≠ [] ∧ (∀ (only: Nat) => sequence = [only] → rank only < rank number))

theorem lengthPositive (xs: List a) (notEmpty: xs ≠ []): 1 ≤ xs.length := match xs with
  | [] => Void.exfalso (notEmpty rfl)
  | [x, ..rest] => omega

--| Each rule of a sequence reads at least a letter.
theorem matchedLength (rules: Rules) (rank: Nat → Nat) (bound: Nat) (ranked: Ranked rules rank bound)
    (sequence: List Nat) (read: List Char) (matched: Matches rules sequence read): sequence.length ≤ read.length :=
  match matched with
    | MatchesNothing => omega
    | MatchesLetter [later := later] [rest := rest] rule laterMatch => omega [matchedLength rules rank bound ranked later rest laterMatch]
    | MatchesAlternative [later := later] [read := first] [rest := rest] sequences rule alternative chosen sequenceMatch laterMatch =>
      let ranking := And.right ranked _ sequences rule alternative chosen
      rewrite List.lengthAppend first rest in
        omega [
          matchedLength rules rank bound ranked later rest laterMatch,
          matchedLength rules rank bound ranked alternative first sequenceMatch,
          lengthPositive alternative (And.left ranking)
        ]

--| Enough fuel for `sequence` to match `read`: a rule alone needs more
--| than its rank beyond `read.length * bound`; in a longer sequence, each
--| rule reads less than all of `read`.
def Fuelled (bound: Nat) (rank: Nat → Nat) (fuel: Nat): (sequence: List Nat) → (read: List Char) → Prop
  | [], read => Unit
  | [only], read => read.length * bound + rank only < fuel
  | [first, second, ..more], read => read.length * bound ≤ fuel

theorem scaleStep (shorter: Nat) (longer: Nat) (bound: Nat) (less: shorter + 1 ≤ longer): shorter * bound + bound ≤ longer * bound :=
  let same: (shorter + 1) * bound = shorter * bound + bound := ring
  omega [Nat.leMulRight (shorter + 1) longer bound less, same]

--| A rule followed by others, with fuel enough for them all: there is
--| enough for the rule's own part, and for the others'.
theorem fuelledSplit (bound: Nat) (rank: Nat → Nat) (below: ∀ (number: Nat) => rank number < bound) (fuel: Nat) (number: Nat)
    (headRead: List Char) (laterRead: List Char) (headLong: 1 ≤ headRead.length)
    (later: List Nat) (long: later.length ≤ laterRead.length) (fuelled: Fuelled bound rank fuel [number, ..later] (headRead ++ laterRead)):
    headRead.length * bound + rank number < fuel ∧ Fuelled bound rank fuel later laterRead := match later with
      | [] =>
        let whole := List.lengthAppend headRead laterRead
        Both (omega [Nat.leMulRight headRead.length (headRead ++ laterRead).length bound (omega [whole])]) Trivial
      | [second] =>
        let whole := List.lengthAppend headRead laterRead
        Both (omega [scaleStep headRead.length (headRead ++ laterRead).length bound (omega [whole]), below number])
          (omega [scaleStep laterRead.length (headRead ++ laterRead).length bound (omega [whole]), below second])
      | [second, third, ..more] =>
        let whole := List.lengthAppend headRead laterRead
        Both (omega [scaleStep headRead.length (headRead ++ laterRead).length bound (omega [whole]), below number])
          (omega [Nat.leMulRight laterRead.length (headRead ++ laterRead).length bound (omega [whole])])

--| Enough fuel for a rule is enough, less one, for each of its
--| alternatives.
theorem fuelledInner (bound: Nat) (rank: Nat → Nat) (more: Nat) (number: Nat) (read: List Char)
    (enough: read.length * bound + rank number < Succ more)
    (alternative: List Nat) (lower: ∀ (only: Nat) => alternative = [only] → rank only < rank number): Fuelled bound rank more alternative read :=
  match alternative with
    | [] => Trivial
    | [only] => omega [lower only rfl]
    | [first, second, ..others] => omega

theorem completeAll (rules: Rules) (rank: Nat → Nat) (bound: Nat) (ranked: Ranked rules rank bound):
    ∀ (sequence: List Nat) (read: List Char) => Matches rules sequence read → ∀ (fuel: Nat) => Fuelled bound rank fuel sequence read →
      ∀ (rest: List Char) => rest ∈ rules.leftAfterAll fuel sequence (read ++ rest)
    := sequence read matched fuel fuelled rest =>
  match matched with
    | MatchesNothing => Inl rfl
    | MatchesLetter [number := number] [later := later] [letter := letter] [rest := laterRead] rule laterMatch =>
      let split := fuelledSplit bound rank (And.left ranked) fuel number [letter] laterRead (omega) later
        (matchedLength rules rank bound ranked later laterRead laterMatch) fuelled
      match fuel with
        | Zero => Void.exfalso (omega [And.left split])
        | Succ more =>
          List.memFlatMapIntro (left => rules.leftAfterAll (Succ more) later left) (laterRead ++ rest) rest
            (rules.leftAfter (Succ more) number ([letter, ..laterRead] ++ rest))
            (rewrite ruleSpec rules number, rule, DecEq.refl letter in Inl rfl)
            (completeAll rules rank bound ranked later laterRead laterMatch (Succ more) (And.right split) rest)
    | MatchesAlternative [number := number] [later := later] [read := headRead] [rest := laterRead] sequences rule alternative chosen sequenceMatch
      laterMatch =>
      let ranking := And.right ranked number sequences rule alternative chosen
      let split := fuelledSplit bound rank (And.left ranked) fuel number headRead laterRead
        (omega [matchedLength rules rank bound ranked alternative headRead sequenceMatch, lengthPositive alternative (And.left ranking)]) later
        (matchedLength rules rank bound ranked later laterRead laterMatch) fuelled
      match fuel with
        | Zero => Void.exfalso (omega [And.left split])
        | Succ more =>
          rewrite List.appendAssoc headRead laterRead rest in
            List.memFlatMapIntro (left => rules.leftAfterAll (Succ more) later left) (laterRead ++ rest) rest
              (rules.leftAfter (Succ more) number (headRead ++ (laterRead ++ rest)))
              (rewrite ruleSpec rules number, rule in
                List.memFlatMapIntro (sequence => rules.leftAfterAll more sequence (headRead ++ (laterRead ++ rest))) alternative (laterRead ++ rest) sequences
                  chosen
                  (completeAll rules rank bound ranked alternative headRead sequenceMatch more
                    (fuelledInner bound rank more number headRead (And.left split) alternative (And.right ranking)) (laterRead ++ rest)))
              (completeAll rules rank bound ranked later laterRead laterMatch (Succ more) (And.right split) rest)
