--| The program's middle (the sorted scores at index length / 2) is a
--| middle score in the spec's sense, for any nonempty list; with an odd
--| number of scores there is only one.

namespace Aoc.Year2021.Day10.Proofs
import Aoc.Year2021.Day10 (..)
import Aoc.Year2021.Day10.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

--| In a sorted list, at most k elements are below the one at index k.
theorem countBelowSorted: ∀ (sorted: List Nat) => List.Sorted Nat.leq sorted
      → ∀ (k: Nat) => k < sorted.length → sorted.count (score => score < sorted.getOr k 0) ≤ k
  | [], s, k, h => cases
  | [x, ..rest], s, Zero, h =>
    let none := List.countNone rest (score => score < x) (y member =>
      arithmetic [List.sortedHeadLe Nat.leq Nat.leTrans x y rest s member])
    rewrite List.countCons rest x (score => score < x), (arithmetic: (x < x) = False), none then Nat.leRefl 0
  | [x, ..rest], Both _ s, Succ k, h =>
    let below := countBelowSorted rest s k h
    let one := Bool.toNatLeOne (x < rest.getOr k 0)
    rewrite List.countCons rest x (score => score < rest.getOr k 0) then arithmetic

--| And at most length - 1 - k above it.
theorem countAboveSorted: ∀ (sorted: List Nat) => List.Sorted Nat.leq sorted
      → ∀ (k: Nat) => k < sorted.length → sorted.count (score => sorted.getOr k 0 < score) + k + 1 ≤ sorted.length
  | [], s, k, h => cases
  | [x, ..rest], s, Zero, h =>
    let most := List.countLeLength rest (score => x < score)
    rewrite List.countCons rest x (score => x < score), (arithmetic: (x < x) = False) then arithmetic
  | [x, ..rest], Both first s, Succ k, h =>
    let above := countAboveSorted rest s k h
    let atMost: x ≤ rest.getOr k 0 := List.sortedGetOrLe [x, ..rest] 0 (Both first s) 0 (Succ k) (arithmetic) h
    rewrite List.countCons rest x (score => rest.getOr k 0 < score), (arithmetic: (rest.getOr k 0 < x) = False) then
      arithmetic

--| The program's middle is a middle score of any nonempty list.
theorem middleIsMiddle ∀ (scores: List Nat) (some: scores ≠ []): Middle scores (middle scores) :=
  let sorted := scores.sort
  let n := scores.length
  let k := n / 2
  let sameLength: sorted.length = n := List.sortLength scores
  let positive: 0 < n := match scores with
    | [] => (some byComputing).impossible
    | [_, .._] => byComputing
  let split := Nat.divModEq n 2
  let rest := Nat.modLess n 2 (arithmetic)
  let inRange: k < sorted.length := arithmetic
  let isSorted := List.sortSortedNat scores
  let m := sorted.getOr k 0
  let member: m ∈ scores := List.memPerm sorted scores (List.sortPerm scores) m (List.getOrMem sorted k 0 inRange)
  let below := countBelowSorted sorted isSorted k inRange
  let above := countAboveSorted sorted isSorted k inRange
  let belowSame := List.countPerm sorted scores (List.sortPerm scores) (score => score < m)
  let aboveSame := List.countPerm sorted scores (List.sortPerm scores) (score => m < score)
  Both member (Both (arithmetic) (arithmetic))

--| The scores that aren't above `a` and those that are make up the list.
theorem countSplit ∀ (a: Nat) (xs: List Nat):
    xs.count (score => not (a < score)) + xs.count (score => a < score) = xs.length :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      let split := countSplit a rest
      rewrite List.countCons rest x (score => not (a < score)), List.countCons rest x (score => a < score) then
        match above: a < x with
          | True | False => arithmetic

--| With an odd number of scores, a middle score can't be below another.
theorem middleNotBelow ∀ (scores: List Nat) (a b: Nat)
    (odd: scores.length % 2 = 1)
    (first: Middle scores a)
    (second: Middle scores b)
    (less: a < b):
    Void :=
  let split := countSplit a scores
  let moreBelowB := List.countLeMem scores (score => not (a < score)) (score => score < b) (score member atMost =>
    match above: a < score with | False => arithmetic)
  let halves := Nat.divModEq scores.length 2
  let aAbove := first.right.right
  let bBelow := second.right.left
  arithmetic

--| With an odd number of scores, the middle score is unique.
theorem middleUnique ∀ (scores: List Nat) (a b: Nat)
    (odd: scores.length % 2 = 1)
    (first: Middle scores a)
    (second: Middle scores b):
    a = b :=
  match less: a < b with
    | True => Void.impossible (middleNotBelow scores a b odd first second less)
    | False =>
      match more: b < a with
        | True => Void.impossible (middleNotBelow scores b a odd second first more)
        | False => arithmetic
