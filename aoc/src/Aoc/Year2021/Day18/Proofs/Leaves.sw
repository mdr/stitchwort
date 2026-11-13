--| The leaves of a number: adding to the leftmost or rightmost regular
--| number is adding to the first or last leaf, and how the spec's list
--| helpers go over `++`.

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Aoc.Year2021.Day18.Spec (Leaf, addToFirst, addToLast, leaves)
import Std (Eq, List, Nat, Void)

--| How many pairs deep a number's deepest regular number is.
def height: Number → Nat
  | Regular _ => 0
  | Pair left right => Nat.max (height left) (height right) + 1

--| A number has at least one leaf.
theorem leavesNotNil ∀ (depth: Nat) (number: Number): leaves depth number ≠ [] := match number with
  | Regular _ => empty => cases
  | Pair left right => empty => List.appendNotNilLeft (leaves (depth + 1) left) (leaves (depth + 1) right) (leavesNotNil (depth + 1) left) empty

theorem addToFirstAppend ∀ (amount: Nat) (ys: List Leaf) (xs: List Leaf) (some: xs ≠ []): addToFirst amount (xs ++ ys) = addToFirst amount xs ++ ys :=
  match xs with
    | [] => Void.exfalso (some rfl)
    | [_, .._] => rfl

theorem addToLastCons ∀ (amount: Nat) (leaf: Leaf) (rest: List Leaf) (some: rest ≠ []): addToLast amount [leaf, ..rest] = [leaf, ..addToLast amount rest] :=
  match rest with
    | [] => Void.exfalso (some rfl)
    | [_, .._] => rfl

theorem addToLastAppend ∀ (amount: Nat) (ys: List Leaf) (some: ys ≠ []) (xs: List Leaf): addToLast amount (xs ++ ys) = xs ++ addToLast amount ys :=
  match xs with
    | [] => rfl
    | [x, ..rest] =>
      rewrite addToLastCons amount x (rest ++ ys) (List.appendNotNilRight rest ys some), addToLastAppend amount ys some rest in rfl

--| Adding 0 to a leaf leaves it as it was.
theorem addZeroLeaf ∀ (leaf: Leaf): ({ value = leaf.value + 0, depth = leaf.depth }: Leaf) = leaf := Leaf.ext { value = leaf.value + 0, depth = leaf.depth } leaf (Nat.addZero leaf.value) rfl

theorem addToFirstZero ∀ (xs: List Leaf): addToFirst 0 xs = xs := match xs with
  | [] => rfl
  | [leaf, ..rest] => Eq.cong (l => [l, ..rest]) (addZeroLeaf leaf)

theorem addToLastZero ∀ (xs: List Leaf): addToLast 0 xs = xs := match xs with
  | [] => rfl
  | [leaf] => Eq.cong (l => [l]) (addZeroLeaf leaf)
  | [leaf, next, ..rest] => Eq.cong (Cons leaf) (addToLastZero [next, ..rest])

theorem leavesAddLeftmost ∀ (amount: Nat) (depth: Nat) (number: Number): leaves depth (addLeftmost amount number) = addToFirst amount (leaves depth number) :=
  match number with
    | Regular value => rfl
    | Pair left right =>
      rewrite leavesAddLeftmost amount (depth + 1) left, addToFirstAppend amount (leaves (depth + 1) right) (leaves (depth + 1) left) (leavesNotNil (depth + 1) left) in rfl

theorem leavesAddRightmost ∀ (amount: Nat) (depth: Nat) (number: Number): leaves depth (addRightmost amount number) = addToLast amount (leaves depth number) :=
  match number with
    | Regular value => rfl
    | Pair left right =>
      rewrite leavesAddRightmost amount (depth + 1) right, addToLastAppend amount (leaves (depth + 1) right) (leavesNotNil (depth + 1) right) (leaves (depth + 1) left) in rfl
