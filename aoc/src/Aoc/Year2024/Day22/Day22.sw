-- Advent of Code 2024, day 22: each buyer's secret number evolves by three
-- steps, each mixing a multiple or fraction of it back in with XOR and
-- pruning it to 24 bits. Part 1 adds up each buyer's 2000th new secret
-- number. Part 2 takes each secret's last digit as a price, and finds the
-- sequence of four price changes that earns the most bananas when every
-- buyer sells at its first occurrence.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day22.main < examples/2024/day22.txt
--
-- The proofs are in `Aoc.Year2024.Day22.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day22.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day22
import Std (Fail, IO, Int, List, Map, Nat, Parse, Text)
import Std.Parse (nat)

def main(): {IO, Fail} () :=
  let buyers := parseBuyers IO.readAll()
  IO.print "Part 1: ${solvePart1 buyers}"
  IO.print "Part 2: ${solvePart2 buyers}"

-- Each buyer's initial secret number, one per line.
def parseBuyers (input: Text): {Fail} (List Nat) := Parse.eachLine input nat

-- Secret numbers are pruned to below this: 2 to the power 24.
def modulus: Nat := 16777216

-- The next secret number: three steps, each mixing in (XOR) the secret
-- times 64, divided by 32, or times 2048, and keeping the low 24 bits. Both
-- sides of each XOR are below the modulus, so its result is too.
def nextSecret (secret: Nat): Nat :=
  let first := (secret * 64 % modulus).xor (secret % modulus)
  let second := (first / 32).xor first
  (second * 2048 % modulus).xor second

-- The initial secret and the `count` secrets after it.
def secrets: (count: Nat) → (secret: Nat) → List Nat
  | Zero, secret => [secret]
  | Succ count, secret => Cons secret (secrets count (nextSecret secret))

def solvePart1 (buyers: List Nat): Nat := buyers.sumBy (buyer => Nat.iterate 2000 nextSecret buyer)

-- Part 2.

-- Four consecutive price changes.
type Changes = { first: Int, second: Int, third: Int, fourth: Int }

def change (before: Nat) (after: Nat): Int := after.toInt - before.toInt

-- A buyer's prices: the last digit of each secret.
def prices (count: Nat) (buyer: Nat): List Nat := secrets count buyer |> .map (% 10)

-- The changes into the fifth of `prices` and that price, if there are five.
def sale (prices: List Nat): Option (Changes, Nat) :=
  match prices with
    | Cons a (Cons b (Cons c (Cons d (Cons e rest)))) => Some ({ first = change a b, second = change b c, third = change c d, fourth = change d e }, e)
    | _ => None

-- Each sequence of changes in `prices`, with the price at its first
-- occurrence.
def firstSales (prices: List Nat): Map Changes Nat :=
  prices.tails
    |> .filterMap sale
    |> .foldLeft Map.empty (sales found => sales.insertWith found.fst found.snd (new old => old))

-- The bananas each sequence of changes earns over all buyers, for those
-- that some buyer's prices show.
def bananasBySequence (count: Nat) (buyers: List Nat): Map Changes Nat :=
  buyers.foldLeft Map.empty (totals buyer => totals.unionWith (firstSales (prices count buyer)) Nat.add)

def bestTotal (count: Nat) (buyers: List Nat): Nat := bananasBySequence count buyers |> .values |> .foldLeft 0 Nat.max

def solvePart2 (buyers: List Nat): Nat := bestTotal 2000 buyers
