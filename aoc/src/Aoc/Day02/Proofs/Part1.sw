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
theorem rangeDoubled (r: Range): sumOfIdsWrittenTwice r = List.sumBy (k => repeatedSpec r k 2) (List.rangeFrom (Nat.digits r.to).length 1) :=
  let size := List.length (Nat.digits r.to)
  calc sumOfIdsWrittenTwice r
    -- (`List.between 1 size` is `List.rangeFrom (size + 1 - 1) 1`)
    _ = List.sumBy (k => RepetitionTemplate.sumIn r { blockLength = k, copies = 2 }) (List.rangeFrom size 1)
      := Eq.cong (n => List.sumBy (k => RepetitionTemplate.sumIn r { blockLength = k, copies = 2 }) (List.rangeFrom n 1)) (omega: size + 1 - 1 = size)
    _ = List.sumBy (k => repeatedSpec r k 2) (List.rangeFrom size 1)
      := List.sumRangeCongr (k => RepetitionTemplate.sumIn r { blockLength = k, copies = 2 }) (k => repeatedSpec r k 2) size 1
        (k k1 k2 => repeatedCorrect r k 2)

-- (b) Part 1 is the brute-force sum over blocks.
theorem part1BlocksCorrect (ranges: List Range): solvePart1 ranges = part1Blocks ranges :=
  List.sumByCong sumOfIdsWrittenTwice (r => List.rangeFrom (Nat.digits r.to).length 1 |> .sumBy (k => repeatedSpec r k 2)) ranges rangeDoubled

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
    List.sumBy (k => repeatedSpec r k 2) (List.rangeFrom (List.length (Nat.digits r.to)) 1) = List.sum (List.filter doubled r.ids) :=
  calc List.sumBy (k => repeatedSpec r k 2) (List.rangeFrom (List.length (Nat.digits r.to)) 1)
    -- block length by block length, the ids whose digits are that block written twice...
    _ = List.sumBy (k => List.sumBy (x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids) (List.rangeFrom (List.length (Nat.digits r.to)) 1)
      := List.sumRangeCongr (k => repeatedSpec r k 2) (k => List.sumBy (x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids)
        (List.length (Nat.digits r.to)) 1 (k h1 h2 => repeatedSpecIds r k h1 2 rfl)
    -- ...id by id, the block lengths that make it...
    _ = List.sumBy (x => List.sumBy (k => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) (List.rangeFrom (List.length (Nat.digits r.to)) 1)) r.ids
      := List.sumBySwap (k x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids (List.rangeFrom (List.length (Nat.digits r.to)) 1)
    -- ...which is the id once if it is doubled, and not at all if not.
    _ = List.sumBy (x => Nat.keepIf x (doubled x)) r.ids
      := List.sumRangeCongr (x => List.sumBy (k => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) (List.rangeFrom (List.length (Nat.digits r.to)) 1))
        (x => Nat.keepIf x (doubled x)) r.size r.from
        (x h1 h2 => collapse x 2 rfl (List.length (Nat.digits r.to)) (idsBelow r x h1 h2))
    _ = List.sum (List.filter doubled r.ids) := Eq.sym (List.sumFilter doubled r.ids)

-- The block walk and the id walk agree on every input.
theorem blocksAreIds (ranges: List Range): part1Blocks ranges = part1Spec ranges :=
  List.sumByCong (r => List.sumBy (k => repeatedSpec r k 2) (List.rangeFrom (List.length (Nat.digits r.to)) 1))
    (r => List.sum (List.filter doubled r.ids)) ranges rangeBlocksIds

-- (c) Part 1 is the sum of the ids, in all the ranges, whose digits are some
-- block written twice.
theorem part1Correct (ranges: List Range): solvePart1 ranges = part1Spec ranges :=
  Eq.trans (part1BlocksCorrect ranges) (blocksAreIds ranges)
