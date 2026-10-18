-- Advent of Code 2025, day 2: product ids. An id is invalid when its decimal
-- digits are some block written twice (part 1) or two or more times (part 2).
-- Sum the invalid ids that lie in any of the given ranges.
--
--   $ stitchwort run aoc/day02.sw < aoc/inputs/day02.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- Rather than test every id, add up the invalid ones arithmetically. The
-- ids made of a k-digit block written r times are base * m for the k-digit
-- bases, where m = 1 + 10^k + 10^2k + ... (12 written 3 times is
-- 12 * 10101). Those bases form an interval, so their sum is an arithmetic
-- series. Part 2 must not count 111111 three times (1 six times, 11 three
-- times, 111 twice): by inclusion-exclusion over r, the ids with some proper
-- period are the sum over r of -mu(r) times the ids with r blocks, where mu
-- is the Moebius function.

-- A range of ids, both ends included.
def parseRange (t : Text) : Maybe (Nat, Nat) :=
  match Text.split '-' t with
    | Cons a (Cons b Nil) => Maybe.andThen (\x => Maybe.map (\y => (x, y)) (Text.toNat b)) (Text.toNat a)
    | _                   => Nothing

def parseRanges (t : Text) : List (Nat, Nat) := (Text.split ',' (Text.trim t)).mapMaybe parseRange

-- The sum of the ids in [a, b] that are a k-digit block written r times.
-- m is the multiplier: 12 written 3 times is 12 * 10101, and 10101 is
-- 1 + 10^2 + 10^4.
def repeated (a : Nat) (b : Nat) (k : Nat) (r : Nat) : Nat :=
  let m := (List.range r).foldl (\acc i => acc + Nat.pow 10 (k * i)) 0
  if h : m != 0
    then
      let lo := Nat.max (Nat.pow 10 (k - 1)) ((a + m - 1) / m)
      let hi := Nat.min (Nat.pow 10 k - 1) (b / m)
      if Nat.leq lo hi then m * ((lo + hi) * (hi - lo + 1) / 2) else 0
    else 0

-- Minus the Moebius function, for the repeat counts 2 to 10.
def weight (r : Nat) : Int :=
  match r with
    | 2  => 1
    | 3  => 1
    | 5  => 1
    | 6  => -1
    | 7  => 1
    | 10 => -1
    | _  => 0

-- Part 1 only wants a block written exactly twice.
def twice (r : Nat) : Int := if r == 2 then 1 else 0

-- The invalid ids in [a, b] under a weighting of the repeat counts: every
-- block size k and repeat count r that fit in b's digits (at most 10, the
-- most the weights cover).
def invalid (w : Nat -> Int) : (Nat, Nat) -> Int
  | (a, b) =>
    let size := List.length (Nat.digits b)
    let terms := (List.rangeFrom size 1).concatMap (\k => ((List.rangeFrom 9 2).filter (\r => Nat.leq (k * r) size)).map (\r => w r * Nat.toInt (repeated a b k r)))
    terms.foldl (\x y => x + y) 0

def total (w : Nat -> Int) (rs : List (Nat, Nat)) : Nat := Int.toNat ((rs.map (invalid w)).foldl (\x y => x + y) 0)

def solve (rs : List (Nat, Nat)) : (Nat, Nat) := (total twice rs, total weight rs)

def main () : {IO} () := report (solve (parseRanges (Text.join ',' (IO.readAllLines ()))))

def report : (Nat, Nat) -> {IO} ()
  | (a, b) =>
    print ("Part 1: " ++ Nat.toText a)
    print ("Part 2: " ++ Nat.toText b)

def example : Text := "11-22,95-115,998-1012,1188511880-1188511890,222220-222224,1698522-1698528,446443-446449,38593856-38593862,565653-565659,824824821-824824827,2121212118-2121212124"

test "example" := solve (parseRanges example) == (1227775554, 4174379265)
test "parse" := parseRanges "4-14,1490-3407\n" == [(4, 14), (1490, 3407)]
test "parse junk" := parseRange "4-x" == Nothing
test "12 written 3 times" := repeated 0 1000000 2 3 == 10101 * ((10 + 99) * 90 / 2)
test "single range" := invalid twice (11, 22) == 33
test "no double counting" := invalid weight (111110, 111112) == 111111
test "period three" := invalid weight (998, 1012) == 999 + 1010
test "empty overlap" := invalid weight (12, 21) == 0

theorem exampleAnswer : solve (parseRanges example) = (1227775554, 4174379265) := rfl

theorem twiceIsWeight : twice 2 = weight 2 := rfl
