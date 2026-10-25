-- Cross-check against brute force: for each example bank, try every choice of
-- k batteries, and take the largest number. For banks of at least k batteries,
-- that is what `maxJoltage k` computes greedily (a shorter bank has no choice
-- of k, and brute force gives 0), and it is also proved (`Aoc.Day03.Proofs`,
-- Proofs/Best.sw). Kept apart from the program, so `stitchwort run Aoc.Day03.main` doesn't check it.

namespace Aoc.Day03.Tests
import Aoc.Day03 (..)
import Std (List, Nat)

-- Every way to pick k batteries of the bank, in order.
def choices: Nat → Bank → List Bank
  | Zero, _ => [[]]
  | Succ _, [] => []
  | Succ k, Cons d rest => (choices k rest).map (Cons d) ++ choices (Succ k) rest

def bruteForce (k: Nat) (bank: Bank): Nat :=
  (choices k bank).map joltageOf |> .foldLeft 0 Nat.max

test "choices" := choices 2 [1, 2, 3] == [[1, 2], [1, 3], [2, 3]]
test "brute force, 2 batteries" := exampleBanks.all (b => maxJoltage 2 b == bruteForce 2 b)
test "brute force, 3 batteries" := exampleBanks.all (b => maxJoltage 3 b == bruteForce 3 b)
test "brute force, 12 batteries" := exampleBanks.all (b => maxJoltage 12 b == bruteForce 12 b)
