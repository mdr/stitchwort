-- Day 2, why part 1 is right, in three steps: the printed part 1 is the
-- brute-force sum over blocks (`part1BlocksCorrect`), which is the puzzle's own
-- sum over ids (`part1Correct`). Part 2 is in Part2.sw. Kept apart from the
-- program, so `stitchwort run Aoc.Day02.main` doesn't check any of it.

namespace Aoc.Day02.Proofs
import Aoc.Common (..)
import Aoc.Common.Proofs (..)
import Aoc.Day02 (..)
import Aoc.Day02.Tests (exampleRanges)
import Std (Bool, Eq, Int, List, Nat, Void)

-- Why part 1 is right (b): `part1BlocksCorrect` says the printed part 1 is
-- `part1Blocks`, the brute-force sum over every range and block length of the
-- blocks written twice; (c) below says that is the puzzle's own sum. Part 2
-- is proved in Proofs/Part2.sw (`Aoc.Day02.Proofs.part2Correct`).

-- Brute force for part 1: in each range, every block length up to the
-- number of digits of `to` (a longer block makes a longer id), every block of
-- that length written twice.
def part1Blocks (ranges: List Range): Nat :=
  ranges |> .sumBy (r => List.rangeFrom (Nat.digits r.to).length 1 |> .sumBy (k => repeatedSpec r k 2))

-- If every block from `low` on makes an id above `to`, none is in the range.
theorem noneInRange (from: Nat) (to: Nat) (w: Nat -> Nat) (low: Nat) (big: (b: Nat) -> low <= b -> Nat.leq (w b) to = False):
    (c: Nat) -> (s: Nat) -> low <= s -> List.sum (List.filter (x => from <= x && x <= to) (List.map w (List.rangeFrom c s))) = 0
  | Zero,   s, h => rfl
  | Succ c, s, h =>
    Eq.trans (Eq.cong List.sum (List.filterSkip (x => from <= x && x <= to) (w s) (List.map w (List.rangeFrom c (Succ s))) (Nat.betweenOver from to (w s) (big s h))))
      (noneInRange from to w low big c (Succ s) (Nat.leTrans low s (Succ s) h (Nat.leSucc s)))

-- A block of k digits written twice has 2k digits, too many when `to` has fewer.
theorem tooLong (r: Range): (k: Nat) -> Nat.leq (k * 2) (List.length (Nat.digits r.to)) = False -> repeatedSpec r k 2 = 0
  | Zero,   h => Void.exfalso (Bool.trueNotFalse h)
  | Succ k, h =>
    noneInRange r.from r.to (b => writeTimes (Succ k) b 2) (Nat.pow 10 k)
      (b hb => Nat.leqFalseOfLess r.to (b * Nat.pow 10 (Succ k) + b)
        (calc r.to
          _ < Nat.pow 10 (List.length (Nat.digits r.to))  := Nat.ltPowTenDigits r.to
          _ <= Nat.pow 10 (k + Succ k)
              := Nat.powMono 9 (List.length (Nat.digits r.to)) (k + Succ k)
                   (calc List.length (Nat.digits r.to)
                     _ <= Succ (k * 2) := Nat.leqFalse (Succ k * 2) (List.length (Nat.digits r.to)) h
                     _ = k + Succ k    := Eq.trans (Eq.cong Succ (Eq.trans (Nat.mulSucc k 1) (Eq.cong (t => k + t) (Nat.mulOne k)))) (Eq.sym (Nat.addSucc k k)))
          _ = Nat.pow 10 k * Nat.pow 10 (Succ k)          := Nat.powAdd 10 k (Succ k)
          _ <= b * Nat.pow 10 (Succ k)                    := Nat.leMulRight (Nat.pow 10 k) b (Nat.pow 10 (Succ k)) hb
          _ <= b * Nat.pow 10 (Succ k) + b                := Nat.leAddRight (b * Nat.pow 10 (Succ k)) b))
      (Nat.pow 10 (Succ k) - Nat.pow 10 k) (Nat.pow 10 k) (Nat.leRefl (Nat.pow 10 k))

-- Copies from 3 on count for nothing in part 1.
theorem otherCopies (r: Range) (k: Nat) (size: Nat): (c: Nat) -> (s: Nat) ->
    List.sumBy (n => if Nat.leq (k * n) size then (if n == 2 then sumMatchingTemplate r { blockLength = k, copies = n } else 0) else 0) (List.rangeFrom c (Succ (Succ (Succ s)))) = 0
  | Zero,   s => rfl
  | Succ c, s =>
    match h: Nat.leq (k * Succ (Succ (Succ s))) size with
      | True  => otherCopies r k size c (Succ s)
      | False => otherCopies r k size c (Succ s)

-- One block length's terms: the block written twice, if it fits.
theorem twiceTerms (r: Range): (k: Nat) -> (size: Nat) -> 1 <= k -> (Nat.leq (k * 2) size = False -> repeatedSpec r k 2 = 0) ->
    List.sumBy (n => if Nat.leq (k * n) size then (if n == 2 then sumMatchingTemplate r { blockLength = k, copies = n } else 0) else 0) (List.rangeFrom (size - 1) 2) = repeatedSpec r k 2
  | Zero,   size,          hk, fits => Void.exfalso (Bool.falseNotTrue hk)
  | Succ k, Zero,          hk, fits => Eq.sym (fits rfl)
  | Succ k, Succ Zero,     hk, fits => Eq.sym (fits rfl)
  | Succ k, Succ (Succ s), hk, fits =>
    let f: Nat -> Nat := n => if Nat.leq (Succ k * n) (Succ (Succ s)) then (if n == 2 then sumMatchingTemplate r { blockLength = Succ k, copies = n } else 0) else 0
    match h: Nat.leq (Succ k * 2) (Succ (Succ s)) with
      | True =>
        -- (the match has already chosen the first term, n = 2)
        calc List.foldLeft (acc n => acc + f n) (0 + sumMatchingTemplate r { blockLength = Succ k, copies = 2 }) (List.rangeFrom s 3)
          _ = 0 + sumMatchingTemplate r { blockLength = Succ k, copies = 2 } + List.sumBy f (List.rangeFrom s 3)
              := List.sumByFrom f (0 + sumMatchingTemplate r { blockLength = Succ k, copies = 2 }) (List.rangeFrom s 3)
          _ = 0 + sumMatchingTemplate r { blockLength = Succ k, copies = 2 } + 0 := rewrite otherCopies r (Succ k) (Succ (Succ s)) s 0
          _ = sumMatchingTemplate r { blockLength = Succ k, copies = 2 } := Eq.trans (Nat.addZero (0 + sumMatchingTemplate r { blockLength = Succ k, copies = 2 })) (Eq.trans (Nat.addComm 0 (sumMatchingTemplate r { blockLength = Succ k, copies = 2 })) (Nat.addZero (sumMatchingTemplate r { blockLength = Succ k, copies = 2 })))
          _ = repeatedSpec r (Succ k) 2 := repeatedCorrect r (Succ k) 2
      | False => Eq.trans (otherCopies r (Succ k) (Succ (Succ s)) s 0) (Eq.sym (fits rfl))

-- One range: the ids written exactly twice are the sum over block lengths
-- of the blocks written twice.
theorem rangeDoubled (r: Range): sumOfInvalidIdsInRange r = List.sumBy (k => repeatedSpec r k 2) (List.rangeFrom (Nat.digits r.to).length 1) :=
  calc sumOfInvalidIdsInRange r
    _ = List.sumBy (template => if template.copies == 2 then sumMatchingTemplate r template else 0) (allTemplatesForRange r)
        := List.sumByFilter (sumMatchingTemplate r) (template => template.copies == 2) (allTemplatesForRange r)
    _ = List.sumBy (k => List.sumBy (n => if Nat.leq (k * n) (List.length (Nat.digits r.to)) then (if n == 2 then sumMatchingTemplate r { blockLength = k, copies = n } else 0) else 0)
          (List.rangeFrom (List.length (Nat.digits r.to) - 1) 2)) (List.rangeFrom (List.length (Nat.digits r.to)) 1)
        := templatesSum r (template => if template.copies == 2 then sumMatchingTemplate r template else 0)
    _ = List.sumBy (k => repeatedSpec r k 2) (List.rangeFrom (Nat.digits r.to).length 1)
        := List.sumRangeCongr (k => List.sumBy (n => if Nat.leq (k * n) (List.length (Nat.digits r.to)) then (if n == 2 then sumMatchingTemplate r { blockLength = k, copies = n } else 0) else 0)
             (List.rangeFrom (List.length (Nat.digits r.to) - 1) 2)) (k => repeatedSpec r k 2) (List.length (Nat.digits r.to)) 1
             (k k1 k2 => twiceTerms r k (List.length (Nat.digits r.to)) k1 (tooLong r k))

-- (b) Part 1 is the brute-force sum over blocks.
theorem part1BlocksCorrect (ranges: List Range): solvePart1 ranges = part1Blocks ranges :=
  List.sumByCong sumOfInvalidIdsInRange (r => List.rangeFrom (Nat.digits r.to).length 1 |> .sumBy (k => repeatedSpec r k 2)) ranges rangeDoubled

-- Why part 1 is right (c): `part1Correct` says the printed part 1 is
-- `part1Spec`, the puzzle's own method: walk every id of every range, keep
-- the ids whose digits are some block written twice (`doubled`), add them up.
--
-- The block walk of (b) adds the same ids. For each block length k it adds
-- the ids whose digits are a k-digit block written twice (`twiceIds`, from
-- `repeatedTwice`'s proof). An id is that for one k at most, half its
-- number of digits (`twiceHalf`), and that k is below the number of digits
-- of `to` (`twiceAtLeast`), so swapping the sums over ids and block lengths
-- leaves each doubled id added once.

def part1Spec (ranges: List Range): Nat :=
  ranges |> .sumBy (r => r.ids |> .filter doubled |> .sum)

test "part 1 spec" := part1Spec exampleRanges == 1227775554

-- For one id `x` up to `to`: over all block lengths, the blocks written twice
-- that make `x` add up to `x` if `x` is doubled, else 0.
theorem idCount (to: Nat) (x: Nat) (hx: x <= to):
    List.sumBy (k => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) (List.rangeFrom (List.length (Nat.digits to)) 1) = Nat.keepIf x (doubled x) :=
  match hd: doubled x with
    | True =>
      List.anyRangeElim (k => writtenAs (Nat.digits x) k 2)
        (List.sumBy (k => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) (List.rangeFrom (List.length (Nat.digits to)) 1) = x)
        (List.length (Nat.digits x)) 1 hd
        (k0 h1 h2 hk0 =>
          List.sumRangeOne (k => writtenAs (Nat.digits x) k 2) (k => x) k0 hk0
            (k hk => Eq.trans (Eq.sym (Nat.halfDouble k))
              (Eq.trans (Eq.cong (t => t / 2) (Eq.trans (twiceHalf x k hk) (Eq.sym (twiceHalf x k0 hk0)))) (Nat.halfDouble k0)))
            (List.length (Nat.digits to)) 1 h1
            (Nat.lessLe k0 (List.length (Nat.digits to))
              (Nat.powTenLt k0 (List.length (Nat.digits to)) x (twiceAtLeast x k0 hk0) (Nat.leTrans (Succ x) (Succ to) (Nat.pow 10 (List.length (Nat.digits to))) hx (Nat.ltPowTenDigits to)))))
    | False =>
      List.sumRangeNone (k => writtenAs (Nat.digits x) k 2) (k => x) (List.length (Nat.digits to)) 1
        (k h1 h2 =>
          match t: writtenAs (Nat.digits x) k 2 with
            | True =>
              Void.exfalso (Bool.trueNotFalse (Eq.trans
                (Eq.sym (List.anyRangeIntro (k => writtenAs (Nat.digits x) k 2) (List.length (Nat.digits x)) 1 k h1
                  (Nat.leCongRight k (k + k) (List.length (Nat.digits x)) (twiceHalf x k t) (Nat.leAddRight k k)) t))
                hd))
            | False => rfl)

-- One range: the block walk is the id walk.
theorem rangeBlocksIds (r: Range):
    List.sumBy (k => repeatedSpec r k 2) (List.rangeFrom (List.length (Nat.digits r.to)) 1) = List.sum (List.filter doubled r.ids) :=
  calc List.sumBy (k => repeatedSpec r k 2) (List.rangeFrom (List.length (Nat.digits r.to)) 1)
    -- block length by block length, the ids whose digits are that block written twice...
    _ = List.sumBy (k => List.sumBy (x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids) (List.rangeFrom (List.length (Nat.digits r.to)) 1)
        := List.sumRangeCongr (k => repeatedSpec r k 2) (k => List.sumBy (x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids)
             (List.length (Nat.digits r.to)) 1 (k h1 h2 => twiceIds r k h1)
    -- ...id by id, the block lengths that make it...
    _ = List.sumBy (x => List.sumBy (k => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) (List.rangeFrom (List.length (Nat.digits r.to)) 1)) r.ids
        := List.sumBySwap (k x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids (List.rangeFrom (List.length (Nat.digits r.to)) 1)
    -- ...which is the id once if it is doubled, and not at all if not.
    _ = List.sumBy (x => Nat.keepIf x (doubled x)) r.ids
        := List.sumRangeCongr (x => List.sumBy (k => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) (List.rangeFrom (List.length (Nat.digits r.to)) 1))
             (x => Nat.keepIf x (doubled x)) (r.to + 1 - r.from) r.from
             (x h1 h2 => idCount r.to x (rangeEnd r.from r.to x h1 h2))
    _ = List.sum (List.filter doubled r.ids) := Eq.sym (List.sumFilter doubled r.ids)

-- The block walk and the id walk agree on every input.
theorem blocksAreIds (ranges: List Range): part1Blocks ranges = part1Spec ranges :=
  List.sumByCong (r => List.sumBy (k => repeatedSpec r k 2) (List.rangeFrom (List.length (Nat.digits r.to)) 1))
    (r => List.sum (List.filter doubled r.ids)) ranges rangeBlocksIds

-- (c) Part 1 is the sum of the ids, in all the ranges, whose digits are some
-- block written twice.
theorem part1Correct (ranges: List Range): solvePart1 ranges = part1Spec ranges :=
  Eq.trans (part1BlocksCorrect ranges) (blocksAreIds ranges)
