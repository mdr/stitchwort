-- Cross-check against brute force: for each example bank, try every choice of
-- k batteries, and take the largest number. That is what `joltage k` computes
-- greedily, and it is also proved (`Aoc.Day03.Proofs`, Proofs/Best.sw). Kept
-- apart from the program, so `stitchwort run Aoc.Day03.main` doesn't check it.

namespace Aoc.Day03.Tests
import Aoc.Day03 (..)
import Std (Fin, List, Nat)

-- Every way to pick k batteries of the bank, in order.
def choices: Nat -> Bank -> List Bank
  | Zero,   _           => [[]]
  | Succ _, []          => []
  | Succ k, Cons d rest => (choices k rest).map (Cons d) ++ choices (Succ k) rest

def bruteForce (k: Nat) (bank: Bank): Nat :=
  (choices k bank).map (c => Nat.fromDigits (c.map Fin.toNat)) |> .foldLeft Nat.max 0

test "choices" := (choices 2 (Bank.parse "123")).map (c => c.map Fin.toNat) == [[1, 2], [1, 3], [2, 3]]
test "brute force, 2 batteries" := (parseBanks example).all (b => joltage 2 b == bruteForce 2 b)
test "brute force, 3 batteries" := (parseBanks example).all (b => joltage 3 b == bruteForce 3 b)
test "brute force, 12 batteries" := (parseBanks example).all (b => joltage 12 b == bruteForce 12 b)
