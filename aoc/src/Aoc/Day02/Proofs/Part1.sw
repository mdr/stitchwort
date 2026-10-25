-- Day 2, why part 1 is right, in three steps: the printed part 1 is the
-- brute-force sum over blocks (`part1BlocksCorrect`), which is the puzzle's own
-- sum over ids (`part1Correct`). Part 2 is in Part2.sw. Kept apart from the
-- program, so `stitchwort run Aoc.Day02.main` doesn't check any of it.

namespace Aoc.Day02.Proofs
import Aoc.Common (..)
import Aoc.Day02 (..)
import Aoc.Day02.Spec (..)
import Std (Eq, List, Nat)

-- Why part 1 is right (b): `part1BlocksCorrect` says the printed part 1 is
-- `part1Blocks`, the brute-force sum over every range and block length of the
-- blocks written twice; (c) below says that is the puzzle's own sum. Part 2
-- is proved in Proofs/Part2.sw (`Aoc.Day02.Proofs.part2Correct`).

-- Brute force for part 1: in each range, every block length up to the
-- number of digits of `to` (a longer block makes a longer id), every block of
-- that length written twice.
def part1Blocks (ranges: List Range): Nat :=
  ranges |> .sumBy (r => List.rangeFrom (Nat.digits r.to).length 1 |> .sumBy (k => repeatedSpec r k 2))

-- One range: the ids written exactly twice are the sum over block lengths
-- of the blocks written twice.
theorem rangeDoubled (r: Range): sumOfIdsWrittenTwice r = List.sumBy (List.rangeFrom (Nat.digits r.to).length 1) (k => repeatedSpec r k 2) :=
  let size := List.length (Nat.digits r.to)
  calc sumOfIdsWrittenTwice r
    -- (`List.between 1 size` is `List.rangeFrom (size + 1 - 1) 1`)
    _ = List.sumBy (List.rangeFrom size 1) (k => RepetitionTemplate.sumIn { blockLength = k, copies = 2 } r)
      := rewrite (omega: size + 1 - 1 = size)
    _ = List.sumBy (List.rangeFrom size 1) (k => repeatedSpec r k 2)
      := rewrite repeatedCorrect r _ 2

-- (b) Part 1 is the brute-force sum over blocks.
theorem part1BlocksCorrect (ranges: List Range): solvePart1 ranges = part1Blocks ranges :=
  rewrite rangeDoubled _

-- Why part 1 is right (c): `part1Correct` says the printed part 1 is
-- `part1Spec`, the puzzle's own method: walk every id of every range, keep
-- the ids whose digits are some block written twice (`doubled`), add them up.
--
-- The block walk of (b) adds the same ids. These are the n-copies lemmas of
-- Repeated.sw at n = 2: for each block length k the block walk adds the ids
-- whose digits are a k-digit block written twice (`repeatedSpecIds`), and
-- swapping the sums over ids and block lengths leaves each doubled id added
-- once (`collapse`; `doubled x` is `copies x 2`).

-- One range: the block walk is the id walk.
theorem rangeBlocksIds (r: Range):
    List.sumBy (List.rangeFrom (List.length (Nat.digits r.to)) 1) (k => repeatedSpec r k 2) = List.sum (List.filter r.ids doubled) :=
  calc List.sumBy (List.rangeFrom (List.length (Nat.digits r.to)) 1) (k => repeatedSpec r k 2)
    -- block length by block length, the ids whose digits are that block written twice...
    _ = List.sumBy (List.rangeFrom (List.length (Nat.digits r.to)) 1) (k => List.sumBy r.ids (x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)))
      := rewrite repeatedSpecIds r _ _ 2
    -- ...id by id, the block lengths that make it...
    _ = List.sumBy r.ids (x => List.sumBy (List.rangeFrom (List.length (Nat.digits r.to)) 1) (k => Nat.keepIf x (writtenAs (Nat.digits x) k 2)))
      := List.sumBySwap r.ids (List.rangeFrom (List.length (Nat.digits r.to)) 1) (k x => Nat.keepIf x (writtenAs (Nat.digits x) k 2))
    -- ...which is the id once if it is doubled, and not at all if not.
    _ = List.sumBy r.ids (x => Nat.keepIf x (doubled x))
      := rewrite collapse _ 2 rfl _ (idsBelow r _ _ _)
    _ = List.sum (List.filter r.ids doubled) := Eq.sym (List.sumFilter r.ids doubled)

-- The block walk and the id walk agree on every input.
theorem blocksAreIds (ranges: List Range): part1Blocks ranges = part1Spec ranges :=
  rewrite rangeBlocksIds _

-- (c) Part 1 is the sum of the ids, in all the ranges, whose digits are some
-- block written twice.
theorem part1Correct (ranges: List Range): solvePart1 ranges = part1Spec ranges :=
  Eq.trans (part1BlocksCorrect ranges) (blocksAreIds ranges)
