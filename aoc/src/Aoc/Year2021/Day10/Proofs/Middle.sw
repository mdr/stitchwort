--| The program's middle (the sorted scores at index length / 2) is a
--| middle score in the spec's sense, for any nonempty list; with an odd
--| number of scores there is only one.

namespace Aoc.Year2021.Day10.Proofs
import Aoc.Year2021.Day10 (..)
import Aoc.Year2021.Day10.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

--| `y < x` is false when `x ≤ y`.
theorem notBelow ∀ (x y: Nat) (h: x ≤ y): (y < x) = False := omega

--| In a sorted list, at most k elements are below the one at index k.
theorem countBelowSorted: ∀ (sorted: List Nat) => List.Sorted Nat.leq sorted
      → ∀ (k: Nat) => k < sorted.length → sorted.count (score => score < sorted.getOr k 0) ≤ k
  | [], s, k, h => cases
  | [x, ..rest], s, Zero, h =>
    let none := List.countNone rest (score => score < x) (y member =>
      notBelow x y (List.sortedHeadLe Nat.leq Nat.leTrans x y rest s member))
    rewrite List.countCons rest x (score => score < x), notBelow x x (Nat.leRefl x), none in Nat.leRefl 0
  | [x, ..rest], Both _ s, Succ k, h =>
    let below := countBelowSorted rest s k h
    let one := Bool.toNatLeOne (x < rest.getOr k 0)
    rewrite List.countCons rest x (score => score < rest.getOr k 0) in omega

--| And at most length - 1 - k above it.
theorem countAboveSorted: ∀ (sorted: List Nat) => List.Sorted Nat.leq sorted
      → ∀ (k: Nat) => k < sorted.length → sorted.count (score => sorted.getOr k 0 < score) + k + 1 ≤ sorted.length
  | [], s, k, h => cases
  | [x, ..rest], s, Zero, h =>
    let most := List.countLeLength rest (score => x < score)
    rewrite List.countCons rest x (score => x < score), notBelow x x (Nat.leRefl x) in omega
  | [x, ..rest], Both first s, Succ k, h =>
    let above := countAboveSorted rest s k h
    let atMost: x ≤ rest.getOr k 0 := List.sortedGetOrLe [x, ..rest] 0 (Both first s) 0 (Succ k) (omega) h
    rewrite List.countCons rest x (score => rest.getOr k 0 < score), notBelow x (rest.getOr k 0) atMost in omega

--| The program's middle is a middle score of any nonempty list.
theorem middleIsMiddle ∀ (scores: List Nat) (some: scores ≠ []): Middle scores (middle scores) :=
  let sorted := scores.sort
  let n := scores.length
  let k := n / 2
  let sameLength: sorted.length = n := List.sortLength scores
  let positive: 0 < n := match scores with
    | [] => Void.exfalso (some rfl)
    | [_, .._] => rfl
  let split := Nat.divModEq n 2
  let rest := Nat.modLess n 2 (omega)
  let inRange: k < sorted.length := omega
  let isSorted := List.sortSortedNat scores
  let m := sorted.getOr k 0
  let member: m ∈ scores := List.memPerm sorted scores (List.sortPerm scores) m (List.getOrMem sorted k 0 inRange)
  let below := countBelowSorted sorted isSorted k inRange
  let above := countAboveSorted sorted isSorted k inRange
  let belowSame := List.countPerm sorted scores (List.sortPerm scores) (score => score < m)
  let aboveSame := List.countPerm sorted scores (List.sortPerm scores) (score => m < score)
  Both member (Both (omega) (omega))

--| The scores that aren't above `a` and those that are make up the list.
theorem countSplit ∀ (a: Nat) (xs: List Nat):
    xs.count (score => not (a < score)) + xs.count (score => a < score) = xs.length :=
  match xs with
    | [] => rfl
    | [x, ..rest] =>
      let split := countSplit a rest
      rewrite List.countCons rest x (score => not (a < score)), List.countCons rest x (score => a < score) in
        match above: a < x with
          | True => omega
          | False => omega

--| With an odd number of scores, a middle score can't be below another.
theorem middleNotBelow ∀ (scores: List Nat) (a b: Nat)
    (odd: scores.length % 2 = 1)
    (first: Middle scores a)
    (second: Middle scores b)
    (less: a < b):
    Void :=
  let split := countSplit a scores
  let moreBelowB := List.countLeMem scores (score => not (a < score)) (score => score < b) (score member atMost =>
    match above: a < score with | False => omega)
  let halves := Nat.divModEq scores.length 2
  let aAbove := And.right (And.right first)
  let bBelow := And.left (And.right second)
  omega

--| With an odd number of scores, the middle score is unique.
theorem middleUnique ∀ (scores: List Nat) (a b: Nat)
    (odd: scores.length % 2 = 1)
    (first: Middle scores a)
    (second: Middle scores b):
    a = b :=
  match less: a < b with
    | True => Void.exfalso (middleNotBelow scores a b odd first second less)
    | False =>
      match more: b < a with
        | True => Void.exfalso (middleNotBelow scores b a odd second first more)
        | False => omega
