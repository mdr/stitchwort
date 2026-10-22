-- Advent of Code 2025, day 2: product ids. An id is invalid when its decimal
-- digits are some block written twice (part 1) or two or more times (part 2).
-- Sum the invalid ids that lie in any of the given ranges.
--
--   $ cd aoc && stitchwort run Aoc.Day02.main < inputs/day02.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- Rather than test every id, add up the invalid ones arithmetically. The
-- ids made of a k-digit block written n times are base * m for the k-digit
-- bases, where m = 1 + 10^k + 10^2k + ... (12 written 3 times is
-- 12 * 10101). Those bases form an interval, so their sum is an arithmetic
-- series. Part 2 must not count 111111 three times (1 six times, 11 three
-- times, 111 twice): by inclusion-exclusion over n, the ids with some proper
-- period are the sum over n of -mu(n) times the ids with n blocks, where mu
-- is the Moebius function. The weights -mu(n) are computed (`weight`, a
-- signed sum over the divisors), so ids of any length work.
--
-- That `repeated` adds up the right ids is proved in `Aoc.Day02.Proofs`
-- (Proofs/Repeated.sw); the tests are in `Aoc.Day02.Tests` (Tests/). `run` checks
-- neither.

namespace Aoc.Day02
import Aoc.Common (Range)
import Std (Int, List, Nat)

def main(): {IO} () :=
  let ranges := parseRanges IO.readAll()
  IO.print "Part 1: ${solvePart1 ranges}"
  IO.print "Part 2: ${solvePart2 ranges}"

-- The weighted sums are signed; both come out as natural numbers.
def solvePart1 (ranges: List Range): Nat := Int.toNat (ranges |> .sumBy (weighted twice))

def solvePart2 (ranges: List Range): Nat := Int.toNat (ranges |> .sumBy (weighted weight))

-- The ids in the range under weights `w` for the repeat counts: for every
-- block length k and repeat count n whose ids fit in the digits of `to`, the
-- ids that are a k-digit block written n times, times `w n`.
def weighted (w: Nat -> Int) (r: Range): Int :=
  let size := (Nat.digits r.to).length
  List.rangeFrom size 1 |> .sumBy (k =>
    List.rangeFrom (size - 1) 2 |> .sumBy (n => if Nat.leq (k * n) size then w n * (repeated r k n).toInt else 0))

-- The weight of repeat count n: 1, less the weights of the divisors of n
-- from 2 to n - 1. For n >= 2 this is minus the Moebius function (weight 0
-- and weight 1 are 1, and are never used). It is chosen so that for every
-- K >= 2 the weights of K's divisors from 2 on (K itself included) add up to
-- 1: an id whose digits are a block written K times, and no fewer, is then
-- counted once. The guard `d < n` always holds; it is there to show that the
-- recursion ends.
def weight (n: Nat): Int
  decreasing n
:=
  1 - (List.rangeFrom (n - 2) 2 |> .sumBy (d => if h: d < n then (if Nat.divides d n then weight d else 0) else 0))

-- Part 1 only wants a block written exactly twice.
def twice (n: Nat): Int := if n == 2 then 1 else 0

-- The sum of the ids in the range that are a k-digit block written n times.
-- m is the multiplier: 12 written 3 times is 12 * 10101, and 10101 is
-- 1 + 10^2 + 10^4.
def repeated (r: Range) (k: Nat) (n: Nat): Nat :=
  let m := List.range n |> .sumBy (i => Nat.pow 10 (k * i))
  if m != 0 then
    let from := Nat.max (Nat.pow 10 (k - 1)) ((r.from + m - 1) / m)
    let to := Nat.min (Nat.pow 10 k - 1) (r.to / m)
    if from <= to then m * ((from + to) * (to - from + 1) / 2) else 0
  else 0

def parseRanges (t: Text): List Range := t.trim.split ',' |> .filterMap Range.parse

-- The puzzle read digit by digit: the specification that the proofs, and the
-- brute-force tests (Tests/BruteForce.sw), compare the arithmetic with. The
-- digits are some block of k digits written n times.
def writtenAs (ds: List Nat) (k: Nat) (n: Nat): Bool := List.concat (List.replicate n (List.take k ds)) == ds

-- Part 1: written twice; part 2: written two or more times.
def doubled (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (k => writtenAs ds k 2)

def repeats (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (k => List.rangeFrom ds.length 2 |> .any (n => writtenAs ds k n))
