-- Advent of Code 2025, day 2: product ids. An id is invalid when its decimal
-- digits are some block written twice (part 1) or two or more times (part 2).
-- Sum the invalid ids that lie in any of the given ranges.
--
--   $ stitchwort run aoc/day02.sw < aoc/inputs/day02.txt
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

def main () : {IO} () :=
  let (one, two) := solve (parseRanges (IO.readAll ()))
  print ("Part 1: " ++ one.toText)
  print ("Part 2: " ++ two.toText)

def solve (ranges : List Range) : (Nat, Nat) := (total twice ranges, total weight ranges)

def total (w : Nat -> Int) (ranges : List Range) : Nat :=
  ranges
    |> .map (.invalid w)
    |> .sumInt
    |> .toNat

-- A range of ids, both ends included.
type Range = { lo : Nat, hi : Nat }

def Range.parse (t : Text) : Maybe Range :=
  match (t.split '-').map Text.toNat with
    | [Just lo, Just hi] => Just { lo, hi }
    | _                  => Nothing

def parseRanges (t : Text) : List Range :=
  t.trim.split ',' |> .mapMaybe Range.parse

-- The sum of the ids in the range that are a k-digit block written n times.
-- m is the multiplier: 12 written 3 times is 12 * 10101, and 10101 is
-- 1 + 10^2 + 10^4.
def Range.repeated (r : Range) (k : Nat) (n : Nat) : Nat :=
  let m := List.range n |> .sumBy (\i => Nat.pow 10 (k * i))
  if m != 0 then
    let lo := Nat.max (Nat.pow 10 (k - 1)) ((r.lo + m - 1) / m)
    let hi := Nat.min (Nat.pow 10 k - 1) (r.hi / m)
    if lo <= hi then m * ((lo + hi) * (hi - lo + 1) / 2) else 0
  else 0

-- Minus the Moebius function, for the repeat counts 2 to 10.
def weight : Nat -> Int
  | 2  => 1
  | 3  => 1
  | 5  => 1
  | 6  => -1
  | 7  => 1
  | 10 => -1
  | _  => 0

-- Part 1 only wants a block written exactly twice.
def twice (n : Nat) : Int := if n == 2 then 1 else 0

-- The invalid ids in the range under a weighting of the repeat counts: every
-- block size k and repeat count n that fit in the digits of `hi` (n is at
-- most 10, the most the weights cover).
def Range.invalid (w : Nat -> Int) (r : Range) : Int :=
  let size := (Nat.digits r.hi).length
  def terms (k : Nat) : List Int :=
    List.rangeFrom 9 2
      |> .filter (\n => k * n <= size)
      |> .map (\n => w n * (r.repeated k n).toInt)
  List.rangeFrom size 1
    |> .concatMap terms
    |> .sumInt

-- Examples -----------------------------------------------------------------

def range (lo hi : Nat) : Range := { lo, hi }

def example : Text := "11-22,95-115,998-1012,1188511880-1188511890,222220-222224,1698522-1698528,446443-446449,38593856-38593862,565653-565659,824824821-824824827,2121212118-2121212124"

test "example" := solve (parseRanges example) == (1227775554, 4174379265)
test "parse" := parseRanges "4-14,1490-3407\n" == [range 4 14, range 1490 3407]
test "parse junk" := Range.parse "4-x" == Nothing
test "12 written 3 times" := (range 0 1000000).repeated 2 3 == 10101 * ((10 + 99) * 90 / 2)
test "single range" := (range 11 22).invalid twice == 33
test "no double counting" := (range 111110 111112).invalid weight == 111111
test "period three" := (range 998 1012).invalid weight == 999 + 1010
test "empty overlap" := (range 12 21).invalid weight == 0

theorem exampleAnswer : solve (parseRanges example) = (1227775554, 4174379265) := rfl

theorem twiceIsWeight : twice 2 = weight 2 := rfl
