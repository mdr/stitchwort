--| Day 1 as the puzzle states it, by trying every choice of entries. The
--| proofs (Proofs/) show the program finds one of these whenever there is one,
--| and the tests (Tests/Spec.sw) run them on the example.

namespace Aoc.Year2020.Day01.Spec
import Std (List)

--| Every choice of three entries, in the order they come: `[1, 2, 3, 4]` gives
--| `(1, 2, 3)`, `(1, 2, 4)`, `(1, 3, 4)` and `(2, 3, 4)`. Like `List.pairs`,
--| two different entries with the same value are two choices.
def triples: List Nat → List (Nat, Nat, Nat)
  | Nil => Nil
  | Cons x rest => (rest.pairs |> .map (((y, z)) => (x, y, z))) ++ triples rest

--| "Find the two entries that sum to 2020 and then multiply those two numbers
--| together": the products of every such pair. The puzzle expects exactly one.
def part1Answers (entries: List Nat): List Nat :=
  entries.pairs |> .filter (((a, b)) => a + b == 2020) |> .map (((a, b)) => a * b)

--| "What is the product of the three entries that sum to 2020?"
def part2Answers (entries: List Nat): List Nat :=
  triples entries |> .filter (((a, b, c)) => a + b + c == 2020) |> .map (((a, b, c)) => a * b * c)
