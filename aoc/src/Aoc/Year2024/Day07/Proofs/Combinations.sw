-- The spec's `combinations` is what the puzzle's "any combination of
-- operators" says: exactly the lists of the right length made of the
-- operators allowed.

namespace Aoc.Year2024.Day07.Proofs
import Aoc.Year2024.Day07 (..)
import Aoc.Year2024.Day07.Spec (..)
import Std (And, Eq, List, Nat, Void)

-- Every list of allowed operators is among the combinations of its length.
theorem combinationsComplete (operators: List Operator): (chosen: List Operator) → ((operator: Operator) → operator ∈ chosen → operator ∈ operators) →
    chosen ∈ combinations operators chosen.length
  | Nil, allowed => Inl rfl
  | Cons operator rest, allowed =>
    List.memFlatMapIntro (other => combinations operators rest.length |> .map (Cons other)) operator (Cons operator rest) operators
      (allowed operator (Inl rfl))
      (List.memMap (combinations operators rest.length) rest (combinationsComplete operators rest (other has => allowed other (Inr has))) (Cons operator))

-- Every combination has the length asked for and only allowed operators.
theorem combinationsSound (operators: List Operator): (count: Nat) → (chosen: List Operator) → chosen ∈ combinations operators count →
    And (chosen.length = count) ((operator: Operator) → operator ∈ chosen → operator ∈ operators)
  | Zero, chosen, listed =>
    match listed with
      | Inl same => rewrite <- same in Both rfl (operator none => Void.exfalso none)
      | Inr none => Void.exfalso none
  | Succ count, chosen, listed =>
    List.anyElim (first => chosen ∈ (combinations operators count |> .map (Cons first))) _ operators
      (List.memFlatMapElim (first => combinations operators count |> .map (Cons first)) chosen operators listed)
      (first firstAllowed inMap =>
        List.anyElim (rest => Cons first rest = chosen) _ (combinations operators count)
          (List.memMapAny (combinations operators count) (Cons first) chosen inMap)
          (rest restListed same =>
            match combinationsSound operators count rest restListed with
              | Both length restAllowed =>
                rewrite <- same in
                  Both (Eq.cong Succ length) (operator has =>
                    match has with
                      | Inl isFirst => rewrite <- isFirst in firstAllowed
                      | Inr inRest => restAllowed operator inRest)))
