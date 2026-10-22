-- Advent of Code 2025, day 2: product ids. An id is invalid when its decimal
-- digits are some block written twice (part 1) or two or more times (part 2).
-- Sum the invalid ids that lie in any of the given ranges.
--
--   $ cd aoc && stitchwort run Aoc.Day02.main < inputs/day02.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- Rather than test every id, add up the invalid ones arithmetically. The
-- ids made of a k-digit block written n times (a template of k by n) are
-- base * m for the k-digit bases, where m = 1 + 10^k + 10^2k + ... (12
-- written 3 times is 12 * 10101). Those bases form an interval, so their sum
-- is an arithmetic series (`sumOfIdsInRangeMatchingTemplate`). Part 2 must not count
-- 111111 three times (1 six times, 11 three times, 111 twice): by
-- inclusion-exclusion over n, the ids with some proper period are the sum
-- over n of -mu(n) times the ids with n copies, where mu is the Moebius
-- function. The weights -mu(n) are computed (`copiesWeight`, a signed sum
-- over the divisors), so ids of any length work.
--
-- That `sumOfIdsInRangeMatchingTemplate` adds up the right ids is proved in
-- `Aoc.Day02.Proofs` (Proofs/Repeated.sw); the tests are in
-- `Aoc.Day02.Tests` (Tests/), both against the puzzle-literal spec in
-- `Aoc.Day02.Spec` (Spec/). `run` checks none of them.

namespace Aoc.Day02
import Aoc.Common (Range)
import Std (Each, Int, List, Nat)
import Std.Each (each, require)

def main(): {IO} () :=
  let ranges := parseRanges IO.readAll()
  IO.print "Part 1: ${solvePart1 ranges}"
  IO.print "Part 2: ${solvePart2 ranges}"

def solvePart1 (ranges: List Range): Nat := ranges.sumBy sumOfIdsWrittenTwice

-- The weighted sum is signed; it comes out as a natural number.
def solvePart2 (ranges: List Range): Nat := Int.toNat (ranges.sumBy sumOfIdsWrittenRepeatedly)

-- An invalid id's digits are a block written several times: its template is the
-- block's length and the number of copies. 121212 is the block 12 written 3
-- times: its template is { blockLength = 2, copies = 3 }.
type RepetitionTemplate = { blockLength: Nat, copies: Nat }

-- What a block is multiplied by to write it out: 12 written 3 times is
-- 12 * 10101, and 10101 is 1 + 10^2 + 10^4.
def RepetitionTemplate.multiplier (template: RepetitionTemplate): Nat :=
  List.range template.copies |> .sumBy (i => Nat.pow 10 (template.blockLength * i))

-- The blocks have blockLength digits: from 10^(blockLength-1) up to 10^blockLength - 1.
def RepetitionTemplate.smallestBlock (template: RepetitionTemplate): Nat := Nat.pow 10 (template.blockLength - 1)
def RepetitionTemplate.largestBlock (template: RepetitionTemplate): Nat := Nat.pow 10 template.blockLength - 1

-- Every template that fits in the digits of the range's end: a block of one or
-- more digits written two or more times. Some may have no ids in the range;
-- `sumOfIdsInRangeMatchingTemplate` gives those 0.
def allTemplatesForRange (range: Range): List RepetitionTemplate := Each.collect (() =>
  let maxDigits := (Nat.digits range.to).length
  let blockLength := each (List.between 1 maxDigits)
  let copies := each (List.between 2 maxDigits)
  require (blockLength * copies <= maxDigits)
  { blockLength, copies })

-- Part 1: the ids in the range written exactly twice.
def sumOfIdsWrittenTwice (range: Range): Nat :=
  allTemplatesForRange range
    |> .filter (template => template.copies == 2)
    |> .sumBy (sumOfIdsInRangeMatchingTemplate range)

-- Part 2: the ids in the range written two or more times, each counted once.
-- 111111 has templates 1×6, 11×3 and 111×2; the weights cancel the repeats.
def sumOfIdsWrittenRepeatedly (range: Range): Int :=
  (allTemplatesForRange range).sumBy (template =>
    let idsTotal := sumOfIdsInRangeMatchingTemplate range template
    let weight := copiesWeight template.copies
    weight * idsTotal.toInt)

-- The weight of a number of copies: 1, less the weights of the divisors of
-- `copies` from 2 to copies - 1. For copies >= 2 this is minus the Moebius
-- function (the weights of 0 and 1 copies are 1, and are never used). It is
-- chosen so that for every K >= 2 the weights of K's divisors from 2 on (K
-- itself included) add up to 1: an id whose digits are a block written K
-- times, and no fewer, is then counted once. The guard `d < copies` always
-- holds; it is there to show that the recursion ends.
def copiesWeight (copies: Nat): Int
  decreasing copies
:=
  let divisorWeights := List.between 2 (copies - 1) |> .sumBy (d =>
    if h: d < copies then (if Nat.divides d copies then copiesWeight d else 0) else 0)
  1 - divisorWeights

-- The sum of the ids in the range whose digits are a block of the template's
-- length written the template's number of copies.
def sumOfIdsInRangeMatchingTemplate (range: Range) (template: RepetitionTemplate): Nat :=
  -- Every such id is a block times the multiplier.
  let multiplier := template.multiplier
  if multiplier != 0 then
    -- The blocks whose id lies in the range: the block times the multiplier is
    -- at least range.from (round up) and at most range.to (round down).
    let firstBlock := Nat.max template.smallestBlock ((range.from + multiplier - 1) / multiplier)
    let lastBlock := Nat.min template.largestBlock (range.to / multiplier)
    if firstBlock <= lastBlock then multiplier * sumBetween firstBlock lastBlock else 0
  else 0

-- first + (first + 1) + ... + last, for first <= last: an arithmetic series,
-- the number of terms times their average.
def sumBetween (first: Nat) (last: Nat): Nat := (first + last) * (last - first + 1) / 2

def parseRanges (t: Text): List Range := t.trim.split ',' |> .filterMap Range.parse
