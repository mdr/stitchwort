--| Reduced numbers, as the spec says it (by their leaves) and as the proofs
--| use it (by height): a sum `reduce` finishes is reduced, and a reduced
--| number is at most four pairs deep.

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Aoc.Year2021.Day18.Spec (IsReduced, Leaf, leaves)
import Std (List, Nat, Option, Void)

--| A number at most four pairs deep with nothing to split has its leaves
--| inside at most four pairs and below 10.
theorem leavesSmall ∀ (depth: Nat) (number: Number)
    (shallow: depth + height number ≤ 4)
    (none: split number = None):
    List.All (leaf => leaf.depth ≤ 4 ∧ leaf.value ≤ 9) (leaves depth number) :=
  match number with
    | Regular value =>
      match small: Nat.leq 10 value with
        | False => Both (Both shallow omega) Trivial
    | Pair left right =>
      match el: split left with
        | None =>
          match er: split right with
            | None =>
              List.allAppend _
                (leaves (depth + 1) left)
                (leaves (depth + 1) right)
                (leavesSmall (depth + 1) left omega el)
                (leavesSmall (depth + 1) right omega er)

--| A number whose leaves are inside at most four pairs is at most four
--| pairs deep.
theorem leavesShallow ∀ (depth: Nat) (number: Number)
    (small: List.All (leaf => leaf.depth ≤ 4 ∧ leaf.value ≤ 9) (leaves depth number)):
    depth + height number ≤ 4 :=
  match number with
    | Regular value => And.left (And.left small)
    | Pair left right =>
      omega [
        leavesShallow
          (depth + 1)
          left
          (List.allAppendLeft _ (leaves (depth + 1) left) (leaves (depth + 1) right) small),
        leavesShallow
          (depth + 1)
          right
          (List.allAppendRight _ (leaves (depth + 1) left) (leaves (depth + 1) right) small)
      ]

theorem reducedHeight ∀ (number: Number) (reduced: IsReduced number): height number ≤ 4 :=
  leavesShallow 0 number reduced
