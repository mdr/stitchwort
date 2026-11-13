--| Part 2: for a machine whose buttons don't move the claw along the same
--| line, `Machine.fewestTokens` is the fewest tokens of any presses that
--| win, or `None` when none do (`fewestTokensCorrect`). The spec's part 2
--| has only one answer (`part2AnswerUnique`).

namespace Aoc.Year2024.Day13.Proofs
import Aoc.Year2024.Day13 (..)
import Aoc.Year2024.Day13.Spec (Fewest, IsFewest, Part2Answer, Unwinnable, correctedMachine, cost, winsPrize)
import Std (And, Bool, Eq, Exists, Int, List, Nat, Option, Void)

theorem costIsTokens (aPresses: Nat) (bPresses: Nat): cost aPresses bPresses = tokens aPresses bPresses := omega

--| Cramer's rule's presses cost the fewest tokens, as they are the only
--| presses that win; when it finds none, none win.
theorem cramerFewest (machine: Machine) (nonzero: machine.determinant ≠ 0):
    IsFewest machine ((machine.onlyPresses nonzero).map (((aPresses, bPresses)) => tokens aPresses bPresses)) :=
  match found: machine.onlyPresses nonzero with
    | Some (aPresses, bPresses) =>
      Both (Witness aPresses (Witness bPresses (Both (onlyPressesWins machine nonzero aPresses bPresses found) (costIsTokens aPresses bPresses))))
        (otherA otherB otherWon =>
          let same := Option.someInjective (Eq.trans (Eq.sym found) (onlyPressesFinds machine nonzero otherA otherB otherWon))
          let sameA: aPresses = otherA := Eq.cong (pair => pair.fst) same
          let sameB: bPresses = otherB := Eq.cong (pair => pair.snd) same
          rewrite costIsTokens otherA otherB, sameA, sameB in Nat.leRefl (tokens otherA otherB))
    | None =>
      (aPresses bPresses =>
        match winning: winsPrize machine aPresses bPresses with
          | True => Void.exfalso (Option.noneNotSome _ (Eq.trans (Eq.sym found) (onlyPressesFinds machine nonzero aPresses bPresses winning)))
          | False => rfl)

theorem fewestTokensCorrect (machine: Machine) (nonzero: machine.determinant ≠ 0): IsFewest machine machine.fewestTokens :=
  match Int.decEq machine.determinant 0 with
    | { holds = True, sound = isZero, complete = _ } => Void.exfalso (nonzero (isZero rfl))
    | { holds = False, sound = _, complete = c } => cramerFewest machine (e => Bool.falseNotTrue (c e))

theorem correctedIsSpec (machine: Machine): machine.corrected = correctedMachine machine := rfl

--| A machine that can be won isn't unwinnable.
theorem winsAgainst (machine: Machine) (tokens: Nat) (fewest: Fewest machine tokens) (unwinnable: Unwinnable machine): Void :=
  match And.left fewest with
    | Witness aPresses (Witness bPresses (Both won costs)) => Bool.falseNotTrue (Eq.trans (Eq.sym (unwinnable aPresses bPresses)) won)

--| The fewest tokens are at most any other fewest.
theorem atMostOther (machine: Machine) (tokens: Nat) (others: Nat) (fewest: Fewest machine tokens) (other: Fewest machine others): tokens ≤ others :=
  match And.left other with
    | Witness aPresses (Witness bPresses (Both won costs)) => rewrite <- costs in And.right fewest aPresses bPresses won

--| A machine has one fewest number of tokens, or none.
theorem fewestUnique (machine: Machine) (first second: Option Nat) (firstFewest: IsFewest machine first) (secondFewest: IsFewest machine second): first = second :=
  match first, second with
    | None, None => rfl
    | Some tokens, None => Void.exfalso (winsAgainst machine tokens firstFewest secondFewest)
    | None, Some tokens => Void.exfalso (winsAgainst machine tokens secondFewest firstFewest)
    | Some tokens, Some others =>
      Eq.cong Some (omega [atMostOther machine tokens others firstFewest secondFewest, atMostOther machine others tokens secondFewest firstFewest])

--| The spec's part 2 has one answer.
theorem part2AnswerUnique (machines: List Machine) (first: Nat) (second: Nat) (firstAnswer: Part2Answer machines first)
    (secondAnswer: Part2Answer machines second): first = second := match firstAnswer with
      | Witness firstFewest (Both firstRight firstSum) =>
        match secondAnswer with
          | Witness secondFewest (Both secondRight secondSum) =>
            rewrite firstSum, secondSum in
              List.sumByCongMem machines _ _ (machine member =>
                rewrite fewestUnique (correctedMachine machine) (firstFewest machine) (secondFewest machine) (firstRight machine member)
                    (secondRight machine member) in
                  rfl)
