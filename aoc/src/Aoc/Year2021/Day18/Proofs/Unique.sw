--| The spec's sums are well defined: reducing ends in one place, and a
--| number is fixed by its leaves, so `x + y` is one number.

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Aoc.Year2021.Day18.Spec (IsSum, Leaf, ReducesTo, leaves)
import Std (Eq, Exists, List, Nat, Option, Void)

--| Reducing ends in one place.
theorem reducesToUnique ∀ (b: List Leaf) (start a: List Leaf) (h: ReducesTo start a) (h1: ReducesTo start b): a = b :=
  match h, h1 with
    | Reduced done, Reduced _ => rfl
    | Reduced done, Steps step _ => Void.exfalso (Option.noneNotSome _ (Eq.trans (Eq.sym done) step))
    | Steps step _, Reduced done => Void.exfalso (Option.noneNotSome _ (Eq.trans (Eq.sym done) step))
    | Steps [next := next1] step1 rest1, Steps [next := next2] step2 rest2 =>
      let same := Option.someInjective (Eq.trans (Eq.sym step1) step2)
      reducesToUnique b next2 a (rewrite same at rest1 in rest1) rest2

def headValue: List Leaf → Nat
  | [] => 0
  | [leaf, .._] => leaf.value

def headDepth: List Leaf → Nat
  | [] => 0
  | [leaf, .._] => leaf.depth

--| A number's first leaf is at least as deep as the number.
theorem leavesHead ∀ (depth: Nat) (number: Number) (rest: List Leaf):
    ∃ (first: Leaf) => ∃ (more: List Leaf) => leaves depth number ++ rest = [first, ..more] ∧ depth ≤ first.depth :=
  match number with
    | Regular value => Witness ({ value, depth }) (Witness rest (Both rfl omega))
    | Pair left right =>
      match leavesHead (depth + 1) left (leaves (depth + 1) right ++ rest) with
        | Witness first (Witness more (Both starts deep)) =>
          Witness first (Witness more (Both (rewrite List.appendAssoc (leaves (depth + 1) left) (leaves (depth + 1) right) rest in starts) omega))

--| A number's leaves start a list in one way only.
theorem leavesPrefix ∀ (depth: Nat) (x y: Number) (rest1 rest2: List Leaf) (same: leaves depth x ++ rest1 = leaves depth y ++ rest2):
    x = y ∧ rest1 = rest2 := match x, y with
      | Regular a, Regular b => Both (rewrite Eq.cong headValue same in rfl) (Eq.cong (xs => List.drop xs 1) same)
      | Regular a, Pair left right =>
        match leavesHead (depth + 1) left (leaves (depth + 1) right ++ rest2) with
          | Witness first (Witness more (Both starts deep)) =>
            let heads := rewrite List.appendAssoc (leaves (depth + 1) left) (leaves (depth + 1) right) rest2, starts at same in Eq.cong headDepth same
            Void.exfalso (omega [heads, deep])
      | Pair left right, Regular b =>
        match leavesHead (depth + 1) left (leaves (depth + 1) right ++ rest1) with
          | Witness first (Witness more (Both starts deep)) =>
            let heads := rewrite List.appendAssoc (leaves (depth + 1) left) (leaves (depth + 1) right) rest1, starts at same in Eq.cong headDepth same
            Void.exfalso (omega [heads, deep])
      | Pair left1 right1, Pair left2 right2 =>
        let split := rewrite List.appendAssoc (leaves (depth + 1) left1) (leaves (depth + 1) right1) rest1, List.appendAssoc (leaves (depth + 1) left2) (leaves (depth + 1) right2) rest2 at same in same
        let lefts := leavesPrefix (depth + 1) left1 left2 (leaves (depth + 1) right1 ++ rest1) (leaves (depth + 1) right2 ++ rest2) split
        let rights := leavesPrefix (depth + 1) right1 right2 rest1 rest2 (And.right lefts)
        Both (rewrite And.left lefts, And.left rights in rfl) (And.right rights)

theorem leavesInjective ∀ (x: Number) (y: Number) (same: leaves 0 x = leaves 0 y): x = y :=
  And.left (leavesPrefix 0 x y [] [] (rewrite List.appendNil (leaves 0 x), List.appendNil (leaves 0 y) in same))

--| `x + y` is one number.
theorem sumUnique ∀ (x: Number) (y: Number) (sum1: Number) (sum2: Number) (first: IsSum x y sum1) (second: IsSum x y sum2): sum1 = sum2 :=
  leavesInjective sum1 sum2 (reducesToUnique (leaves 0 sum2) (leaves 0 (Pair x y)) (leaves 0 sum1) first second)
