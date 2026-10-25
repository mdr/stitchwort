-- Advent of Code 2025, day 2: product ids. An id is invalid when its decimal
-- digits are some block written twice (part 1) or two or more times (part 2).
-- Sum, range by range, the invalid ids in each of the given ranges (an id in two
-- overlapping ranges counts twice; the puzzle input's ranges don't overlap).
--
--   $ cd aoc && stitchwort run Aoc.Day02.main < inputs/day02.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- Rather than test every id, add up the invalid ones arithmetically. The
-- ids made of a k-digit block written n times (a template of k by n) are
-- base * m for the k-digit bases, where m = 1 + 10^k + 10^2k + ... (12
-- written 3 times is 12 * 10101). Those bases form an interval, so their sum
-- is an arithmetic series (`RepetitionTemplate.sumIn`). Part 2 must not count
-- 111111 three times (1 six times, 11 three times, 111 twice): by
-- inclusion-exclusion over n, the ids with some proper period are the sum
-- over n of -mu(n) times the ids with n copies, where mu is the Moebius
-- function. The weights -mu(n) are computed (`copiesWeight`, a signed sum
-- over the divisors), so ids of any length work.
--
-- That `RepetitionTemplate.sumIn` adds up the right ids is proved in
-- `Aoc.Day02.Proofs` (Proofs/Repeated.sw); the tests are in
-- `Aoc.Day02.Tests` (Tests/), both against the puzzle-literal spec in
-- `Aoc.Day02.Spec` (Spec/). `run` checks none of them.

namespace Aoc.Day02
import Aoc.Common (Range)
import Std (Each, Fail, Int, List, Nat)
import Std.Each (each, require)

def main(): {IO, Fail} () :=
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
-- `RepetitionTemplate.sumIn` gives those 0.
def allTemplatesForRange (range: Range): List RepetitionTemplate := Each.collect (() =>
  let maxDigits := (Nat.digits range.to).length
  let blockLength := each (List.between 1 maxDigits)
  let copies := each (List.between 2 maxDigits)
  require (blockLength * copies ≤ maxDigits)
  { blockLength, copies })

-- Part 1: the ids in the range written exactly twice: add up, over the block
-- lengths, the ids that are a block of that length written twice. A block
-- longer than half the digits of the range's end has no ids in the range,
-- and `RepetitionTemplate.sumIn` gives 0.
def sumOfIdsWrittenTwice (range: Range): Nat :=
  List.between 1 (Nat.digits range.to).length
    |> .sumBy (blockLength => RepetitionTemplate.sumIn { blockLength, copies = 2 } range)

-- Part 2: the ids in the range written two or more times, each counted once.
-- 111111 has templates 1×6, 2×3 and 3×2 (block length × copies); the weights cancel the repeats.
def sumOfIdsWrittenRepeatedly (range: Range): Int :=
  (allTemplatesForRange range).sumBy (template =>
    let idsTotal := RepetitionTemplate.sumIn template range
    let weight := copiesWeight template.copies
    weight * idsTotal.toInt)

-- The weight of a number of copies: 1, less the weights of the divisors of
-- `copies` from 2 to copies - 1. For copies >= 2 this is minus the Moebius
-- function (the weights of 0 and 1 copies are 1, and are never used). It is
-- chosen so that for every K >= 2 the weights of K's divisors from 2 on (K
-- itself included) add up to 1: an id whose smallest repeating block is written K
-- times is then counted once. The guard `d < copies` always holds; it is
-- there to show that the recursion ends.
def copiesWeight (copies: Nat): Int
    decreasing copies
:=
  let divisorWeights := List.between 2 (copies - 1) |> .sumBy (divisor =>
    if h: divisor < copies then (if Nat.divides divisor copies then copiesWeight divisor else 0) else 0)
  1 - divisorWeights

-- The sum of the ids in the range whose digits are a block of the template's
-- length written the template's number of copies.
def RepetitionTemplate.sumIn (template: RepetitionTemplate) (range: Range): Nat :=
  -- Every such id is a block times the multiplier.
  let multiplier := template.multiplier
  if multiplier ≠ 0 then
    -- The blocks whose id lies in the range: the block times the multiplier is
    -- at least range.from (round up) and at most range.to (round down). When
    -- no block fits, firstBlock > lastBlock and `Nat.sumBetween` gives 0.
    let firstBlock := Nat.max template.smallestBlock (Nat.ceilDiv range.from multiplier)
    let lastBlock := Nat.min template.largestBlock (range.to / multiplier)
    multiplier * Nat.sumBetween firstBlock lastBlock
  else 0

-- Ranges separated by commas. Spaces and a final line ending are allowed;
-- anything else fails, naming the text that isn't a range.
def parseRanges (text: Text): {Fail} (List Range) := text.trim.split ',' |> .map Range.parse
