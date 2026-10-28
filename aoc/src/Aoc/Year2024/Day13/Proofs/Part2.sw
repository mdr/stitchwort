-- Part 2: for a machine whose buttons don't move the claw along the same
-- line, `Machine.fewestTokens` is the fewest tokens of any presses that
-- win, or `None` when none do (`fewestTokensCorrect`). The spec's part 2
-- has only one answer (`part2AnswerUnique`).

namespace Aoc.Year2024.Day13.Proofs
import Aoc.Year2024.Day13 (..)
import Aoc.Year2024.Day13.Spec (Fewest, IsFewest, Part2Answer, Unwinnable, correctedMachine, cost, winsPrize)
import Std (And, Bool, Eq, Exists, Int, List, Nat, Option, Void)

theorem costIsTokens (aPresses: Nat) (bPresses: Nat): cost aPresses bPresses = tokens aPresses bPresses := omega

theorem noneNotSome (value: a) (h: None = Some value): Void := Bool.falseNotTrue (Eq.cong (option => Option.isSome option) h)

-- Cramer's rule's presses cost the fewest tokens, as they are the only
-- presses that win; when it finds none, none win.
theorem cramerFewest (machine: Machine) (nonzero: machine.determinant ≠ 0):
    IsFewest machine ((machine.onlyPresses nonzero).map (((aPresses, bPresses)) => tokens aPresses bPresses)) :=
  match found: machine.onlyPresses nonzero with
    | Some (aPresses, bPresses) =>
      Both (Witness aPresses (Witness bPresses (Both (onlyPressesWins machine nonzero aPresses bPresses found) (costIsTokens aPresses bPresses))))
        (otherA otherB otherWon =>
          let same := Option.someInjective _ _ (Eq.trans (Eq.sym found) (onlyPressesFinds machine nonzero otherA otherB otherWon))
          let sameA: aPresses = otherA := Eq.cong (pair => pair.fst) same
          let sameB: bPresses = otherB := Eq.cong (pair => pair.snd) same
          rewrite costIsTokens otherA otherB, sameA, sameB in Nat.leRefl (tokens otherA otherB))
    | None =>
      (aPresses bPresses =>
        match winning: winsPrize machine aPresses bPresses with
          | True => Void.exfalso (noneNotSome _ (Eq.trans (Eq.sym found) (onlyPressesFinds machine nonzero aPresses bPresses winning)))
          | False => rfl)

theorem fewestTokensCorrect (machine: Machine) (nonzero: machine.determinant ≠ 0): IsFewest machine machine.fewestTokens :=
  match Int.decEq machine.determinant 0 with
    | Yes isZero => Void.exfalso (nonzero isZero)
    | No proof => cramerFewest machine proof

theorem correctedIsSpec (machine: Machine): machine.corrected = correctedMachine machine := rfl

-- A machine that can be won isn't unwinnable.
theorem winsAgainst (machine: Machine) (tokens: Nat) (fewest: Fewest machine tokens) (unwinnable: Unwinnable machine): Void :=
  match And.left fewest with
    | Witness aPresses (Witness bPresses (Both won costs)) => Bool.falseNotTrue (Eq.trans (Eq.sym (unwinnable aPresses bPresses)) won)

-- The fewest tokens are at most any other fewest.
theorem atMostOther (machine: Machine) (tokens: Nat) (others: Nat) (fewest: Fewest machine tokens) (other: Fewest machine others): tokens ≤ others :=
  match And.left other with
    | Witness aPresses (Witness bPresses (Both won costs)) => rewrite <- costs in And.right fewest aPresses bPresses won

-- A machine has one fewest number of tokens, or none.
theorem fewestUnique (machine: Machine): (first: Option Nat) → (second: Option Nat) → IsFewest machine first → IsFewest machine second → first = second
  | None, None, firstFewest, secondFewest => rfl
  | Some tokens, None, firstFewest, secondFewest => Void.exfalso (winsAgainst machine tokens firstFewest secondFewest)
  | None, Some tokens, firstFewest, secondFewest => Void.exfalso (winsAgainst machine tokens secondFewest firstFewest)
  | Some tokens, Some others, firstFewest, secondFewest =>
    Eq.cong Some (omega [atMostOther machine tokens others firstFewest secondFewest, atMostOther machine others tokens secondFewest firstFewest])

-- Sums that agree on every element.
theorem sumByAgree (f: a → Nat) (g: a → Nat): (xs: List a) → ((x: a) → x ∈ xs → f x = g x) → xs.sumBy f = xs.sumBy g
  | Nil, agree => rfl
  | Cons x rest, agree =>
    rewrite List.sumByCons rest x f, List.sumByCons rest x g, agree x (Inl rfl), sumByAgree f g rest (y member => agree y (Inr member)) in rfl

-- The spec's part 2 has one answer.
theorem part2AnswerUnique (machines: List Machine) (first: Nat) (second: Nat) (firstAnswer: Part2Answer machines first)
    (secondAnswer: Part2Answer machines second): first = second :=
  match firstAnswer with
    | Witness firstFewest (Both firstRight firstSum) =>
      match secondAnswer with
        | Witness secondFewest (Both secondRight secondSum) =>
          rewrite firstSum, secondSum in
            sumByAgree _ _ machines (machine member =>
              rewrite fewestUnique (correctedMachine machine) (firstFewest machine) (secondFewest machine) (firstRight machine member)
                  (secondRight machine member) in
                rfl)
