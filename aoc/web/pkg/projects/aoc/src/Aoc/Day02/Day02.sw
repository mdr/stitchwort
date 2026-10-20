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
-- is the Moebius function. The weights -mu(n) are computed (`plus`, `minus`),
-- so ids of any length work.
--
-- That `repeated` adds up the right ids is proved in `Aoc.Day02.Proofs`
-- (Proofs/Repeated.sw).

namespace Aoc.Day02
import Aoc.Common (Range)

def main(): {IO} () :=
  let ranges := parseRanges (IO.readAll())
  IO.print "Part 1: ${solvePart1 ranges}"
  IO.print "Part 2: ${solvePart2 ranges}"

def solvePart1 (ranges: List Range): Nat := ranges |> .sumBy (weighted twice)

def solvePart2 (ranges: List Range): Nat := ranges |> .sumBy invalid

-- One range: the ids counted with a plus, less those counted with a minus.
def invalid (r: Range): Nat := weighted plus r - weighted minus r

-- The ids in the range under weights `w` for the repeat counts: for every
-- block length k and repeat count n whose ids fit in the digits of `to`, the
-- ids that are a k-digit block written n times, times `w n`.
def weighted (w: Nat -> Nat) (r: Range): Nat :=
  let size := (Nat.digits r.to).length
  List.rangeFrom size 1 |> .sumBy (\k =>
    List.rangeFrom (size - 1) 2 |> .sumBy (\n => if Nat.leq (k * n) size then w n * repeated r k n else 0))

-- The weights. Repeat count n has weight `plus n - minus n` (minus the
-- Moebius function), chosen so that for every K >= 2 the weights of the
-- divisors of K from 2 on add up to 1:
--
--   plus K  = 1 + (minus d, added up over the divisors d of K with 2 <= d < K)
--   minus K =     (plus d,  added up over the same divisors)
--
-- The two parts are kept apart so that everything is a natural number.
-- `weightFuel fuel True n` is `plus n` and `weightFuel fuel False n` is
-- `minus n`; the fuel makes the recursion structural, and n + 1 is enough.
def plus (n: Nat): Nat := weightFuel (Succ n) True n

def minus (n: Nat): Nat := weightFuel (Succ n) False n

def weightFuel: Nat -> Bool -> Nat -> Nat
  | Zero,   s,     n => 0
  | Succ f, True,  n => 1 + divisorWeights (\d => weightFuel f False d) n (n - 2)
  | Succ f, False, n => divisorWeights (\d => weightFuel f True d) n (n - 2)

-- The weights w of the divisors of m among 2, 3, ..., c + 1, added up. (An
-- `if` rather than `Nat.keepIf`, so that only the divisors' weights are computed.)
def divisorWeights (w: Nat -> Nat) (m: Nat) (c: Nat): Nat :=
  List.rangeFrom c 2 |> .sumBy (\d => if Nat.divides d m then w d else 0)

test "weights" := List.map (\n => (plus n).toInt - (minus n).toInt) (List.rangeFrom 11 2) == [1, 1, 0, 1, -1, 1, 0, 0, -1, 1, 0]

-- Part 1 only wants a block written exactly twice.
def twice (n: Nat): Nat := if n == 2 then 1 else 0

test "single range" := weighted twice (range 11 22) == 33
test "no double counting" := invalid (range 111110 111112) == 111111
test "period three" := invalid (range 998 1012) == 999 + 1010
test "empty overlap" := invalid (range 12 21) == 0

-- The sum of the ids in the range that are a k-digit block written n times.
-- m is the multiplier: 12 written 3 times is 12 * 10101, and 10101 is
-- 1 + 10^2 + 10^4.
def repeated (r: Range) (k: Nat) (n: Nat): Nat :=
  let m := List.range n |> .sumBy (\i => Nat.pow 10 (k * i))
  if m != 0 then
    let from := Nat.max (Nat.pow 10 (k - 1)) ((r.from + m - 1) / m)
    let to := Nat.min (Nat.pow 10 k - 1) (r.to / m)
    if from <= to then m * ((from + to) * (to - from + 1) / 2) else 0
  else 0

test "12 written 3 times" := repeated { from = 0, to = 1000000 } 2 3 == 10101 * ((10 + 99) * 90 / 2)

def parseRanges (t: Text): List Range := t.trim.split ',' |> .mapMaybe Range.parse

def example: Text := "11-22,95-115,998-1012,1188511880-1188511890,222220-222224,1698522-1698528,446443-446449,38593856-38593862,565653-565659,824824821-824824827,2121212118-2121212124"

def range (from to: Nat): Range := { from, to }

def exampleRanges: List Range := parseRanges example

test "example" := (solvePart1 exampleRanges, solvePart2 exampleRanges) == (1227775554, 4174379265)
test "parse" := parseRanges "4-14,1490-3407\n" == [range 4 14, range 1490 3407]

-- Cross-check against brute force ---------------------------------------
--
-- Both parts compared with the obvious method on many small ranges: look at
-- every id's digits. (Both are also proved, in `Aoc.Day02.Proofs`: part 1 in
-- Proofs/Part1.sw, part 2 in Proofs/Part2.sw; `run` does not check them.)

-- The digits are some block of k digits written n times.
def writtenAs (ds: List Nat) (k: Nat) (n: Nat): Bool := List.concat (List.replicate n (List.take k ds)) == ds

test "written as" := (writtenAs [1, 2, 1, 2] 2 2, writtenAs [1, 2, 1, 2] 1 4, writtenAs [1, 1, 1] 1 3) == (True, False, True)

-- Part 1: written twice; part 2: written two or more times.
def doubled (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (\k => writtenAs ds k 2)

def repeats (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (\k => List.rangeFrom ds.length 2 |> .any (\n => writtenAs ds k n))

def bruteSum (invalid: Nat -> Bool) (r: Range): Nat :=
  r.ids |> .filter invalid |> .sum

def agrees (r: Range): Bool :=
  weighted twice r == bruteSum doubled r && invalid r == bruteSum repeats r

-- Ranges of 40 ids starting every 13 up to 2000, and some that cross into
-- more digits.
def checkRanges: List Range :=
  (List.rangeFrom 154 0 |> .map (\i => range (13 * i) (13 * i + 39)))
    ++ [range 95 115, range 990 1010, range 9990 10010, range 99990 100010, range 111100 111200, range 999990 1000010]

test "brute force agrees" := checkRanges.all agrees

-- Ids of 11 to 20 digits, around 1 written 11, 12 and 13 times, 12 written 6
-- times, 1234 written 3 times, 17 ones, 10 written 10 times, and across into
-- 12 digits: part 2 against walking the ids.
def longRanges: List Range :=
  [range 11111111100 11111111120, range 111111111101 111111111121, range 1111111111100 1111111111120,
   range 121212121202 121212121222, range 123412341224 123412341244, range 99999999989 100000000009,
   range 11111111111111101 11111111111111121, range 10101010101010101000 10101010101010101020]

test "long ids" := longRanges.all (\r => invalid r == bruteSum repeats r)
test "long ids found" := List.map invalid longRanges == [11111111111, 111111111111, 1111111111111, 121212121212, 123412341234, 99999999999, 11111111111111111, 10101010101010101010]
