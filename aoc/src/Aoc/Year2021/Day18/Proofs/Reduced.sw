--| Reduced numbers, as the spec says it (by their leaves) and as the proofs
--| use it (by height): a sum `reduce` finishes is reduced, and a reduced
--| number is at most four pairs deep.

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Aoc.Year2021.Day18.Spec (IsReduced, Leaf, leaves)
import Std (List, Nat, Option, Void)

--| A number at most four pairs deep with nothing to split has its leaves
--| inside at most four pairs and below 10.
theorem leavesSmall (depth: Nat): (number: Number) → depth + height number ≤ 4 → split number = None →
    List.All (leaf => leaf.depth ≤ 4 ∧ leaf.value ≤ 9) (leaves depth number)
  | Regular value, shallow, none =>
    match small: Nat.leq 10 value with
      | True => Void.exfalso (Option.someNotNone _ none)
      | False => Both (Both shallow omega) Trivial
  | Pair left right, shallow, none =>
    match el: split left with
      | Some _ => Void.exfalso (Option.someNotNone _ none)
      | None =>
        match er: split right with
          | Some _ => Void.exfalso (Option.someNotNone _ none)
          | None =>
            List.allAppend _ (leaves (depth + 1) left) (leaves (depth + 1) right) (leavesSmall (depth + 1) left omega el) (leavesSmall (depth + 1) right omega er)

--| A number whose leaves are inside at most four pairs is at most four
--| pairs deep.
theorem leavesShallow (depth: Nat): (number: Number) → List.All (leaf => leaf.depth ≤ 4 ∧ leaf.value ≤ 9) (leaves depth number) → depth + height number ≤ 4
  | Regular value, small => And.left (And.left small)
  | Pair left right, small =>
    omega [
      leavesShallow (depth + 1) left (List.allAppendLeft _ (leaves (depth + 1) left) (leaves (depth + 1) right) small),
      leavesShallow (depth + 1) right (List.allAppendRight _ (leaves (depth + 1) left) (leaves (depth + 1) right) small)
    ]

theorem reducedHeight (number: Number) (reduced: IsReduced number): height number ≤ 4 := leavesShallow 0 number reduced
