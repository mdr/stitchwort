-- Advent of Code 2025, day 3: each line is a bank of batteries with a digit
-- on each. Pick k batteries, in order, to make the largest k-digit number
-- (2 digits in part 1, 12 in part 2). Sum the best number over the banks.
--
--   $ stitchwort run aoc/day03.sw < aoc/inputs/day03.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- Greedy: the first digit is the largest one in the part of the bank that
-- still leaves k - 1 digits after it, taking the leftmost such digit so the
-- most is left over; then repeat on what follows it.

def parseBank (t : Text) : List Nat := (Text.toList t).mapMaybe Char.digitValue

-- The digits of the largest k-digit number that is a subsequence of ds.
def best : Nat -> List Nat -> List Nat
  | Zero,   ds          => Nil
  | Succ k, Nil         => Nil
  | Succ k, Cons d rest =>
    -- The leftmost largest of the next w digits, and what follows it. The
    -- candidate so far is c, followed by `after`.
    def pick : Nat -> List Nat -> Nat -> List Nat -> (Nat, List Nat)
      | Zero,   ds,          c, after => (c, after)
      | Succ w, Nil,         c, after => (c, after)
      | Succ w, Cons x more, c, after =>
        if c < x then pick w more x more else pick w more c after
    let (top, after) := pick (List.length rest - k) rest d rest
    Cons top (best k after)

def joltage (k : Nat) (line : Text) : Nat := Nat.fromDigits (best k (parseBank line))

def total (k : Nat) (lines : List Text) : Nat := (lines.map (joltage k)).sum

def solve (lines : List Text) : (Nat, Nat) := (total 2 lines, total 12 lines)

def main () : {IO} () := report (solve (IO.readAllLines ()))

def report : (Nat, Nat) -> {IO} ()
  | (a, b) =>
    print ("Part 1: " ++ Nat.toText a)
    print ("Part 2: " ++ Nat.toText b)

def example : List Text := ["987654321111111", "811111111111119", "234234234234278", "818181911112111"]

test "example" := solve example == (357, 3121910778619)
test "banks part 1" := example.map (joltage 2) == [98, 89, 78, 92]
test "banks part 2" := example.map (joltage 12) == [987654321111, 811111111119, 434234234278, 888911112111]
test "parse" := parseBank "102" == [1, 0, 2]
test "zeros" := best 2 [0, 0, 5, 0] == [5, 0]
test "leftmost wins" := best 1 [3, 9, 9, 1] == [9]
test "keep everything" := best 3 [4, 5, 6] == [4, 5, 6]
test "too short" := best 5 [1, 2] == [1, 2]

theorem exampleAnswer : solve example = (357, 3121910778619) := rfl

theorem bestNone : best 0 [1, 2, 3] = Nil := rfl

theorem bestAll : best 3 [4, 5, 6] = [4, 5, 6] := rfl
