--| The matcher is sound, with any fuel: whatever `leftAfter` says can be
--| left of a message, the rule matched the part of the message before it.

namespace Aoc.Year2020.Day19.Proofs
import Aoc.Year2020.Day19 (..)
import Aoc.Year2020.Day19.Spec (..)
import Std (Char, DecEq, Eq, Exists, List, Option, Void)

theorem ruleSpec (rules: Rules) (number: Nat): rules.rule number = ruleNumbered rules number := rfl

--| `read` can start a match of `number` followed by any sequence.
def Leads (rules: Rules) (number: Nat) (read: List Char): Prop :=
  ∀ (later: List Nat) (rest: List Char) => Matches rules later rest → Matches rules [number, ..later] (read ++ rest)

--| What a rule leaves comes after a part of the message it matched.
def LeavesAfter (rules: Rules) (fuel: Nat) (number: Nat): Prop :=
  ∀ (message left: List Char) => left ∈ rules.leftAfter fuel number message →
    ∃ (read: List Char) => message = read ++ left ∧ Leads rules number read

theorem soundAll (rules: Rules) (fuel: Nat) (leaves: ∀ (number: Nat) => LeavesAfter rules fuel number)
    (sequence: List Nat) (message left: List Char) (found: left ∈ rules.leftAfterAll fuel sequence message):
    ∃ (read: List Char) => message = read ++ left ∧ Matches rules sequence read := match sequence, found with
      | [], Inl same => Witness [] (Both same MatchesNothing)
      | [], Inr never => Void.exfalso never
      | [number, ..later], found =>
        match (List.memFlatMap (left => rules.leftAfterAll fuel later left) left (rules.leftAfter fuel number message)).forward found with
          | Witness middle (Both first rest) =>
            match leaves number message middle first with
              | Witness firstRead (Both split leads) =>
                match soundAll rules fuel leaves later middle left rest with
                  | Witness restRead (Both restSplit matched) =>
                    Witness (firstRead ++ restRead)
                      (Both (rewrite split, restSplit in Eq.sym (List.appendAssoc firstRead restRead left)) (leads later restRead matched))

theorem sound (rules: Rules) (fuel number: Nat): LeavesAfter rules fuel number
    := message left found =>
  match fuel with
    | Succ more =>
      match looked: rules.rule number with
        | Some (Letter letter) =>
          match message with
            | [first, ..rest] =>
              match same: first == letter with
                | True =>
                  match found with
                    | Inl leftIsRest =>
                      Witness [letter]
                        (Both (rewrite same.read, leftIsRest in rfl) (later restRead matched => MatchesLetter looked matched))
                    | Inr never => Void.exfalso never
        | Some (Alternatives sequences) =>
          match (List.memFlatMap (sequence => rules.leftAfterAll more sequence message) left sequences).forward found with
            | Witness sequence (Both chosen inner) =>
              match soundAll rules more (sound rules more) sequence message left inner with
                | Witness read (Both split matched) =>
                  Witness read (Both split (later rest laterMatch => MatchesAlternative sequences looked sequence chosen matched laterMatch))
