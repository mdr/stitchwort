-- Advent of Code 2025, day 2: product ids. An id is invalid when its decimal
-- digits are some block written twice (part 1) or two or more times (part 2).
-- Sum the invalid ids that lie in any of the given ranges.
--
--   $ cd aoc && stitchwort run Aoc.Day02.main < inputs/day02.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- Rather than test every id, add up the invalid ones arithmetically. The
-- ids made of a k-digit block written n times are base * m for the k-digit
-- bases, where m = 1 + 10^k + 10^2k + ... (12 written 3 times is
-- 12 * 10101). Those bases form an interval, so their sum is an arithmetic
-- series. Part 2 must not count 111111 three times (1 six times, 11 three
-- times, 111 twice): by inclusion-exclusion over n, the ids with some proper
-- period are the sum over n of -mu(n) times the ids with n blocks, where mu
-- is the Moebius function.

namespace Aoc.Day02
import Aoc.Common (Range, writeTimes)

def main(): {IO} () :=
  let ranges := parseRanges (IO.readAll())
  print "Part 1: ${solvePart1 ranges}"
  print "Part 2: ${solvePart2 ranges}"

def solvePart1 (ranges: List Range): Nat := total twice ranges

def solvePart2 (ranges: List Range): Nat := total weight ranges

def total (w: Nat -> Int) (ranges: List Range): Nat :=
  ranges
    |> .map (Range.invalid w)
    |> .sumInt
    |> .toNat

def parseRanges (t: Text): List Range :=
  t.trim.split ',' |> .mapMaybe Range.parse

def example: Text := "11-22,95-115,998-1012,1188511880-1188511890,222220-222224,1698522-1698528,446443-446449,38593856-38593862,565653-565659,824824821-824824827,2121212118-2121212124"

def range (lo hi: Nat): Range := { lo, hi }

test "example" := (solvePart1 (parseRanges example), solvePart2 (parseRanges example)) == (1227775554, 4174379265)
test "parse" := parseRanges "4-14,1490-3407\n" == [range 4 14, range 1490 3407]

-- Minus the Moebius function, for the repeat counts 2 to 10.
def weight: Nat -> Int
  | 2  => 1
  | 3  => 1
  | 5  => 1
  | 6  => -1
  | 7  => 1
  | 10 => -1
  | _  => 0

-- Part 1 only wants a block written exactly twice.
def twice (n: Nat): Int := if n == 2 then 1 else 0

test "twice is weight at 2" := twice 2 == weight 2

test "single range" := Range.invalid twice (range 11 22) == 33
test "no double counting" := Range.invalid weight (range 111110 111112) == 111111
test "period three" := Range.invalid weight (range 998 1012) == 999 + 1010
test "empty overlap" := Range.invalid weight (range 12 21) == 0


-- Cross-check against brute force ---------------------------------------
--
-- Part 2's inclusion-exclusion isn't proved; instead it's compared with the
-- obvious method on many small ranges: look at every id's digits.

-- The digits are some block of k digits written n times.
def writtenAs (ds: List Nat) (k: Nat) (n: Nat): Bool := List.concat (List.replicate n (List.take k ds)) == ds

-- Part 1: written twice; part 2: written two or more times.
def doubled (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (\k => writtenAs ds k 2)

def repeats (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (\k => List.rangeFrom ds.length 2 |> .any (\n => writtenAs ds k n))

def bruteSum (invalid: Nat -> Bool) (r: Range): Nat :=
  List.rangeFrom (r.hi + 1 - r.lo) r.lo |> .filter invalid |> .sum

def agrees (r: Range): Bool :=
  Range.invalid twice r == (bruteSum doubled r).toInt && Range.invalid weight r == (bruteSum repeats r).toInt

-- Ranges of 40 ids starting every 13 up to 2000, and some that cross into
-- more digits.
def checkRanges: List Range :=
  (List.rangeFrom 154 0 |> .map (\i => range (13 * i) (13 * i + 39)))
    ++ [range 95 115, range 990 1010, range 9990 10010, range 99990 100010, range 111100 111200, range 999990 1000010]

test "brute force agrees" := checkRanges.all agrees

-- Why part 1 is right (b): `part1Correct` says the printed part 1 is
-- `part1Spec`, the brute-force sum over every range and block length of the
-- blocks written twice. Part 2's inclusion-exclusion isn't proved (see the
-- cross-check above).

-- Brute force for part 1: in each range, every block length up to the
-- number of digits of `hi` (a longer block makes a longer id), every block of
-- that length written twice.
def part1Spec (ranges: List Range): Nat :=
  ranges |> .sumBy (\r => List.rangeFrom (Nat.digits r.hi).length 1 |> .sumBy (\k => Range.repeatedSpec r k 2))

-- If every block from `low` on makes an id above `hi`, none is in the range.
theorem noneInRange (lo: Nat) (hi: Nat) (w: Nat -> Nat) (low: Nat) (big: (b: Nat) -> low <= b -> Nat.leq (w b) hi = False):
    (c: Nat) -> (s: Nat) -> low <= s -> List.sum (List.filter (\x => lo <= x && x <= hi) (List.map w (List.rangeFrom c s))) = 0
  | Zero,   s, h => rfl
  | Succ c, s, h =>
    Eq.trans (Eq.cong List.sum (List.filterSkip (\x => lo <= x && x <= hi) (w s) (List.map w (List.rangeFrom c (Succ s))) (Nat.betweenOver lo hi (w s) (big s h))))
      (noneInRange lo hi w low big c (Succ s) (Nat.leTrans low s (Succ s) h (Nat.leSucc s)))

-- A block of k digits written twice has 2k digits, too many when `hi` has fewer.
theorem tooLong (r: Range): (k: Nat) -> Nat.leq (k * 2) (List.length (Nat.digits r.hi)) = False -> Range.repeatedSpec r k 2 = 0
  | Zero,   h => Void.exfalso (Bool.trueNotFalse h)
  | Succ k, h =>
    noneInRange r.lo r.hi (\b => writeTimes (Succ k) b 2) (Nat.pow 10 k)
      (\b hb => Nat.leqFalseOfLess r.hi (b * Nat.pow 10 (Succ k) + b)
        (Nat.leTrans (Succ r.hi) (Nat.pow 10 (List.length (Nat.digits r.hi))) (b * Nat.pow 10 (Succ k) + b) (Nat.ltPowTenDigits r.hi)
          (Nat.leTrans (Nat.pow 10 (List.length (Nat.digits r.hi))) (Nat.pow 10 (k + Succ k)) (b * Nat.pow 10 (Succ k) + b)
            (Nat.powMono 9 (List.length (Nat.digits r.hi)) (k + Succ k)
              (Nat.leCongRight (List.length (Nat.digits r.hi)) (Succ (k * 2)) (k + Succ k)
                (Eq.trans (Eq.cong Succ (Eq.trans (Nat.mulSucc k 1) (Eq.cong (\t => k + t) (Nat.mulOne k)))) (Eq.sym (Nat.addSucc k k)))
                (Nat.leqFalse (Succ k * 2) (List.length (Nat.digits r.hi)) h)))
            (Nat.leCongLeft (Nat.pow 10 k * Nat.pow 10 (Succ k)) (Nat.pow 10 (k + Succ k)) (b * Nat.pow 10 (Succ k) + b) (Eq.sym (Nat.powAdd 10 k (Succ k)))
              (Nat.leTrans (Nat.pow 10 k * Nat.pow 10 (Succ k)) (b * Nat.pow 10 (Succ k)) (b * Nat.pow 10 (Succ k) + b)
                (Nat.leMulRight (Nat.pow 10 k) b (Nat.pow 10 (Succ k)) hb)
                (Nat.leAddRight (b * Nat.pow 10 (Succ k)) b))))))
      (Nat.pow 10 (Succ k) - Nat.pow 10 k) (Nat.pow 10 k) (Nat.leRefl (Nat.pow 10 k))

-- Repeat counts other than 2 count for nothing in part 1.
theorem laterCounts (r: Range) (k: Nat) (size: Nat): (a: Int) -> (c: Nat) -> (s: Nat) ->
    List.foldLeft Int.add a (List.map (\n => twice n * (Range.repeated r k n).toInt) (List.filter (\n => k * n <= size) (List.rangeFrom c (Succ (Succ (Succ s)))))) = a
  | a, Zero,   s => rfl
  | a, Succ c, s =>
    Bool.inspect (k * Succ (Succ (Succ s)) <= size)
      (\u => List.foldLeft Int.add a (List.map (\n => twice n * (Range.repeated r k n).toInt) (List.filter (\n => k * n <= size) (List.rangeFrom (Succ c) (Succ (Succ (Succ s)))))) = a)
      (\h => Eq.trans (Eq.cong (\xs => List.foldLeft Int.add a (List.map (\n => twice n * (Range.repeated r k n).toInt) xs))
          (List.filterKeep (\n => k * n <= size) (Succ (Succ (Succ s))) (List.rangeFrom c (Succ (Succ (Succ (Succ s))))) h))
        (Eq.trans (laterCounts r k size (Int.add a (Nat.toInt 0)) c (Succ s)) (Int.addZero a)))
      (\h => Eq.trans (Eq.cong (\xs => List.foldLeft Int.add a (List.map (\n => twice n * (Range.repeated r k n).toInt) xs))
          (List.filterSkip (\n => k * n <= size) (Succ (Succ (Succ s))) (List.rangeFrom c (Succ (Succ (Succ (Succ s))))) h))
        (laterCounts r k size a c (Succ s)))

-- One block length's terms: the block written twice, if it fits.
theorem termsSum (r: Range) (k: Nat) (size: Nat) (a: Nat) (fits: Nat.leq (k * 2) size = False -> Range.repeatedSpec r k 2 = 0):
    List.foldLeft Int.add (Nat.toInt a) (Range.invalid.terms twice r size k) = Nat.toInt (a + Range.repeatedSpec r k 2) :=
  Bool.inspect (k * 2 <= size)
    (\u => List.foldLeft Int.add (Nat.toInt a) (Range.invalid.terms twice r size k) = Nat.toInt (a + Range.repeatedSpec r k 2))
    (\h => Eq.trans (Eq.cong (\xs => List.foldLeft Int.add (Nat.toInt a) (List.map (\n => twice n * (Range.repeated r k n).toInt) xs))
        (List.filterKeep (\n => k * n <= size) 2 (List.rangeFrom 8 3) h))
      (Eq.trans (laterCounts r k size (Int.add (Nat.toInt a) (twice 2 * (Range.repeated r k 2).toInt)) 8 0)
        (Eq.cong (\t => Nat.toInt (a + t)) (Eq.trans (Nat.addZero (Range.repeated r k 2)) (Range.repeatedCorrect r k 2)))))
    (\h => Eq.trans (Eq.cong (\xs => List.foldLeft Int.add (Nat.toInt a) (List.map (\n => twice n * (Range.repeated r k n).toInt) xs))
        (List.filterSkip (\n => k * n <= size) 2 (List.rangeFrom 8 3) h))
      (Eq.trans (laterCounts r k size (Nat.toInt a) 8 0)
        (Eq.cong (\t => Nat.toInt t) (Eq.sym (Eq.trans (Eq.cong (\t => a + t) (fits (Eq.trans (Eq.sym (Bool.decTrueToBool (Nat.leq (k * 2) size))) h))) (Nat.addZero a))))))

theorem rangeTerms (r: Range) (size: Nat) (fits: (k: Nat) -> Nat.leq (k * 2) size = False -> Range.repeatedSpec r k 2 = 0):
    (ks: List Nat) -> (a: Nat) ->
    List.foldLeft Int.add (Nat.toInt a) (List.concatMap (Range.invalid.terms twice r size) ks)
      = Nat.toInt (List.foldLeft (\acc k => acc + Range.repeatedSpec r k 2) a ks)
  | Nil,       a => rfl
  | Cons k ks, a =>
    Eq.trans (List.foldLeftAppend Int.add (Nat.toInt a) (Range.invalid.terms twice r size k) (List.concatMap (Range.invalid.terms twice r size) ks))
      (Eq.trans (Eq.cong (\z => List.foldLeft Int.add z (List.concatMap (Range.invalid.terms twice r size) ks)) (termsSum r k size a (fits k)))
        (rangeTerms r size fits ks (a + Range.repeatedSpec r k 2)))

theorem invalidTwice (r: Range):
    Range.invalid twice r = Nat.toInt (List.rangeFrom (Nat.digits r.hi).length 1 |> .sumBy (\k => Range.repeatedSpec r k 2)) :=
  rangeTerms r (List.length (Nat.digits r.hi)) (tooLong r) (List.rangeFrom (List.length (Nat.digits r.hi)) 1) 0

theorem totalTwice: (ranges: List Range) -> (a: Nat) ->
    List.foldLeft Int.add (Nat.toInt a) (List.map (Range.invalid twice) ranges)
      = Nat.toInt (List.foldLeft (\acc r => acc + (List.rangeFrom (Nat.digits r.hi).length 1 |> .sumBy (\k => Range.repeatedSpec r k 2))) a ranges)
  | Nil,       a => rfl
  | Cons r rs, a =>
    Eq.trans (Eq.cong (\t => List.foldLeft Int.add (Int.add (Nat.toInt a) t) (List.map (Range.invalid twice) rs)) (invalidTwice r))
      (totalTwice rs (a + (List.rangeFrom (Nat.digits r.hi).length 1 |> .sumBy (\k => Range.repeatedSpec r k 2))))

-- (b) Part 1 is the brute-force sum.
theorem part1Correct (ranges: List Range): solvePart1 ranges = part1Spec ranges :=
  Eq.cong Int.toNat (totalTwice ranges 0)
