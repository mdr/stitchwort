-- Day 1 as the puzzle states it. The proofs (Proofs/) show the program
-- computes these, for every pair of lists.

namespace Aoc.Day01.Spec
import Aoc.Day01 (..)
import Std (List, Nat)

-- "Pair up the smallest number in the left list with the smallest number in
-- the right list, then the second-smallest left number with the
-- second-smallest right number, and so on." `inOrder` is `ids` lined up from
-- smallest to largest: the same ids, each no larger than the next.
type LinedUp (ids: List Nat) (inOrder: List Nat): Prop = {
  increasing: List.Sorted Nat.leq inOrder,
  sameIds: List.Perm inOrder ids
}

-- "Within each pair, figure out how far apart the two numbers are; you'll
-- need to add up all of those distances." The lists are lined up already.
def totalDistance (leftInOrder: List Nat) (rightInOrder: List Nat): Nat :=
  leftInOrder.zipWith rightInOrder Nat.absDiff |> .sum

-- "Calculate a total similarity score by adding up each number in the left
-- list after multiplying it by the number of times that number appears in the
-- right list."
def similarityScore (lists: LocationLists): Nat :=
  lists.left.sumBy (id => id * lists.right.count (== id))
