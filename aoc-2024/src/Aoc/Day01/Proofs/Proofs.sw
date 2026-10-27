-- Day 1 proved, for every pair of lists: part 1 pairs the lists lined up
-- from smallest to largest, whatever order they came in, and part 2's lookups
-- in a count map are the puzzle's "times that number appears".

namespace Aoc.Day01.Proofs
import Aoc.Day01 (..)
import Aoc.Day01.Spec (..)
import Std (Eq, List, Map, Nat)

theorem leqTrans (x: Nat) (y: Nat) (z: Nat) (h1: Nat.leq x y = True) (h2: Nat.leq y z = True): Nat.leq x z = True := omega

theorem leqAntisymm (x: Nat) (y: Nat) (h1: Nat.leq x y = True) (h2: Nat.leq y x = True): x = y := omega

-- Sorting lines a list up.
theorem sortLinesUp (ids: List Nat): LinedUp ids ids.sort := { increasing = List.sortSortedNat ids, sameIds = List.sortPerm ids }

-- A list lines up only one way: as it sorts.
theorem linedUpIsSort (ids: List Nat) (inOrder: List Nat) (h: LinedUp ids inOrder): inOrder = ids.sort :=
  List.sortedPermEq Nat.leq leqTrans leqAntisymm inOrder ids.sort h.increasing (List.sortSortedNat ids)
    (List.permTrans inOrder ids ids.sort h.sameIds (List.permSym ids.sort ids (List.sortPerm ids)))

-- Part 1 is the total distance between the lists lined up.
theorem part1Correct (lists: LocationLists) (leftInOrder: List Nat) (rightInOrder: List Nat)
    (leftLinedUp: LinedUp lists.left leftInOrder) (rightLinedUp: LinedUp lists.right rightInOrder):
    solvePart1 lists = totalDistance leftInOrder rightInOrder :=
  rewrite linedUpIsSort lists.left leftInOrder leftLinedUp, linedUpIsSort lists.right rightInOrder rightLinedUp in rfl

-- So the order the ids come in makes no difference to part 1.
theorem part1AnyOrder (lists: LocationLists) (left: List Nat) (right: List Nat)
    (sameLeft: List.Perm left lists.left) (sameRight: List.Perm right lists.right):
    solvePart1 { left = left, right = right } = solvePart1 lists :=
  part1Correct { left = left, right = right } lists.left.sort lists.right.sort
    { increasing = List.sortSortedNat lists.left, sameIds = List.permTrans lists.left.sort lists.left left (List.sortPerm lists.left) (List.permSym left lists.left sameLeft) }
    { increasing = List.sortSortedNat lists.right, sameIds = List.permTrans lists.right.sort lists.right right (List.sortPerm lists.right) (List.permSym right lists.right sameRight) }

-- Part 2 is the similarity score.
theorem part2Correct (lists: LocationLists): solvePart2 lists = similarityScore lists :=
  List.sumByCong lists.left (id => id * Map.getOr (Map.counts lists.right) id 0) (id => id * lists.right.count (== id))
    (id => rewrite Map.getOrCounts id lists.right, Map.Spec.sameKeyDecide id _ in rfl)

-- And the order the ids come in makes no difference to part 2.
theorem part2AnyOrder (lists: LocationLists) (left: List Nat) (right: List Nat)
    (sameLeft: List.Perm left lists.left) (sameRight: List.Perm right lists.right):
    solvePart2 { left = left, right = right } = solvePart2 lists :=
  rewrite part2Correct { left = left, right = right }, part2Correct lists in
  calc similarityScore { left = left, right = right }
    _ = left.sumBy (id => id * lists.right.count (== id))
      := List.sumByCong left (id => id * right.count (== id)) (id => id * lists.right.count (== id)) (id => rewrite List.countOccurrences right (== id), List.countOccurrences lists.right (== id), sameRight (== id) in rfl)
    _ = similarityScore lists := sumByPerm (id => id * lists.right.count (== id)) left lists.left sameLeft
