--| Day 1 as the puzzle states it, by trying every choice of entries. The
--| proofs (Proofs/) show the program finds one of these whenever there is one,
--| and the tests (Tests/Spec.sw) run them on the example.

namespace Aoc.Year2020.Day01.Spec
import Std (List)

--| "Find the two entries that sum to 2020 and then multiply those two numbers
--| together": the products of every such pair. The puzzle expects exactly one.
def part1Answers (entries: List Nat): List Nat :=
  entries.pairs |> .filter (((a, b)) => a + b == 2020) |> .map (((a, b)) => a * b)

--| "What is the product of the three entries that sum to 2020?": the products
--| of every choice of three entries (in the order they come, like the pairs)
--| that sums to 2020.
def part2Answers (entries: List Nat): List Nat :=
  entries.combinations 3 |> .filter (choice => choice.sum == 2020) |> .map (choice => choice.product)
