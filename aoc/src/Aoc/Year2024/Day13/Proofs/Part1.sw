-- Part 1: `fewestTokensWithin 100` is the spec's least cost over every
-- press count from 0 to 100, for every machine (`withinCorrect`). With a
-- nonzero determinant the
-- spec's costs are all of the one win Cramer's rule finds, if it is within
-- 100 presses; with a zero determinant the program searches as the spec does.

namespace Aoc.Year2024.Day13.Proofs
import Aoc.Year2024.Day13 (..)
import Aoc.Year2024.Day13.Spec (part1, winningCosts)
import Std (And, Bool, Decidable, Eq, Exists, Int, List, Nat, Option, Void)

-- Presses of at most 100 each that win for `tokensSpent`.
def WinWithin (machine: Machine) (tokensSpent: Nat): Prop :=
  ∃ (aPresses: Nat) => ∃ (bPresses: Nat) =>
    aPresses ≤ 100 ∧ bPresses ≤ 100 ∧ wins machine aPresses bPresses = True ∧ tokensSpent = tokens aPresses bPresses

-- B's press counts that win after `aPresses` of A, and what they cost.
def costsAfter (machine: Machine) (aPresses: Nat): List Nat :=
  List.range 101 |> .filter (bPresses => wins machine aPresses bPresses) |> .map (bPresses => tokens aPresses bPresses)

-- Every cost the spec lists is of presses that win, each at most 100.
theorem winningCostsWin (machine: Machine) (tokensSpent: Nat) (listed: tokensSpent ∈ winningCosts machine): WinWithin machine tokensSpent :=
  List.anyElim (aPresses => tokensSpent ∈ costsAfter machine aPresses) (WinWithin machine tokensSpent) (List.range 101)
    (List.memFlatMapElim (costsAfter machine) tokensSpent (List.range 101) listed) (aPresses aListed inner =>
      let winning := (bPresses: Nat) => wins machine aPresses bPresses
      let filtered := List.range 101 |> .filter winning
      List.anyElim (bPresses => tokens aPresses bPresses = tokensSpent) (WinWithin machine tokensSpent) filtered
        (List.memMapAny filtered (bPresses => tokens aPresses bPresses) tokensSpent inner) (bPresses bListed costs =>
          let bWins := List.memFilter (List.range 101) winning bPresses bListed
          let aBelow := And.right (List.memRangeFrom aPresses 101 0 aListed)
          let bBelow := And.right (List.memRangeFrom bPresses 101 0 (And.left bWins))
          Witness aPresses (Witness bPresses (Both (omega) (Both (omega) (Both (And.right bWins) (Eq.sym costs)))))))

-- The spec lists the cost of every win within 100 presses.
theorem winListed (machine: Machine) (aPresses: Nat) (bPresses: Nat) (aWithin: aPresses ≤ 100) (bWithin: bPresses ≤ 100)
    (won: wins machine aPresses bPresses = True): tokens aPresses bPresses ∈ winningCosts machine :=
  let winning := (bPresses: Nat) => wins machine aPresses bPresses
  let filtered := List.range 101 |> .filter winning
  let bListed := List.memFilterIntro (List.range 101) winning bPresses (List.memRangeFromIntro bPresses 101 0 (omega) (omega)) won
  List.memFlatMapIntro (costsAfter machine) aPresses (tokens aPresses bPresses) (List.range 101)
    (List.memRangeFromIntro aPresses 101 0 (omega) (omega)) (List.memMap filtered bPresses bListed (bPresses => tokens aPresses bPresses))

-- Two wins are the same presses, with a nonzero determinant.
theorem sameWin (machine: Machine) (nonzero: determinant machine ≠ 0) (aPresses: Nat) (bPresses: Nat) (otherA: Nat) (otherB: Nat)
    (found: onlyPresses machine nonzero = Some (aPresses, bPresses)) (won: wins machine otherA otherB = True):
    And (otherA = aPresses) (otherB = bPresses) :=
  let same := Option.someInjective _ _ (Eq.trans (Eq.sym found) (onlyPressesFinds machine nonzero otherA otherB won))
  Both (Eq.sym (Eq.cong (pair => pair.fst) same)) (Eq.sym (Eq.cong (pair => pair.snd) same))

-- Cramer's rule within 100 presses gives the least of any list that holds
-- the cost of each win within 100 presses and nothing else. (The list is a
-- variable so that the spec's isn't computed while checking.)
theorem cramerWithinCosts (machine: Machine) (nonzero: determinant machine ≠ 0) (costs: List Nat)
    (costsWin: (tokensSpent: Nat) → tokensSpent ∈ costs → WinWithin machine tokensSpent)
    (winsListed: (aPresses: Nat) → (bPresses: Nat) → aPresses ≤ 100 → bPresses ≤ 100 → wins machine aPresses bPresses = True →
      tokens aPresses bPresses ∈ costs):
    (onlyPresses machine nonzero
      |> .filter (((aPresses, bPresses)) => aPresses ≤ 100 && bPresses ≤ 100)
      |> .map (((aPresses, bPresses)) => tokens aPresses bPresses))
      = costs.minimum :=
  match found: onlyPresses machine nonzero with
    | Some (aPresses, bPresses) =>
      match within: aPresses ≤ 100 && bPresses ≤ 100 with
        | True =>
          let aWithin: aPresses ≤ 100 := Bool.andLeft _ _ within
          let bWithin: bPresses ≤ 100 := Bool.andRight _ _ within
          let won := onlyPressesWins machine nonzero aPresses bPresses found
          Eq.sym (minimumAllEqual (tokens aPresses bPresses) costs (winsListed aPresses bPresses aWithin bWithin won)
            (tokensSpent listed =>
              match costsWin tokensSpent listed with
                | Witness otherA (Witness otherB (Both aBelow (Both bBelow (Both otherWon costs)))) =>
                  let same := sameWin machine nonzero aPresses bPresses otherA otherB found otherWon
                  rewrite costs, And.left same, And.right same in rfl))
        | False =>
          Eq.sym (minimumEmpty costs (tokensSpent listed =>
            match costsWin tokensSpent listed with
              | Witness otherA (Witness otherB (Both aBelow (Both bBelow (Both otherWon costs)))) =>
                let same := sameWin machine nonzero aPresses bPresses otherA otherB found otherWon
                let aWithin: aPresses ≤ 100 := omega [And.left same]
                let bWithin: bPresses ≤ 100 := omega [And.right same]
                Bool.falseNotTrue (Eq.trans (Eq.sym within) (Bool.andIntro (Nat.leq aPresses 100) (Nat.leq bPresses 100) aWithin bWithin))))
    | None =>
      Eq.sym (minimumEmpty costs (tokensSpent listed =>
        match costsWin tokensSpent listed with
          | Witness otherA (Witness otherB (Both aBelow (Both bBelow (Both won costs)))) =>
            noneNotSome _ (Eq.trans (Eq.sym found) (onlyPressesFinds machine nonzero otherA otherB won))))

-- The program's search is the spec's.
theorem searchIsSpec (machine: Machine): searchTokens 100 machine = Aoc.Year2024.Day13.Spec.fewestTokens machine := rfl

-- Each machine's part 1 tokens are the least of the costs, whatever its
-- determinant, for costs as `cramerWithinCosts` has them that the search
-- also finds the least of.
theorem withinCosts (machine: Machine) (costs: List Nat) (costsWin: (tokensSpent: Nat) → tokensSpent ∈ costs → WinWithin machine tokensSpent)
    (winsListed: (aPresses: Nat) → (bPresses: Nat) → aPresses ≤ 100 → bPresses ≤ 100 → wins machine aPresses bPresses = True →
      tokens aPresses bPresses ∈ costs)
    (searched: searchTokens 100 machine = costs.minimum): fewestTokensWithin 100 machine = costs.minimum :=
  match Int.decEq (determinant machine) 0 with
    | Yes isZero => searched
    | No nonzero => cramerWithinCosts machine nonzero costs costsWin winsListed

theorem withinCorrect (machine: Machine): fewestTokensWithin 100 machine = Aoc.Year2024.Day13.Spec.fewestTokens machine :=
  withinCosts machine (winningCosts machine) (winningCostsWin machine) (winListed machine) (searchIsSpec machine)
