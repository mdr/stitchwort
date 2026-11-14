--| Day 1 as the puzzle states it. The proofs (Proofs/) show the program
--| computes these, for every list of depths.

namespace Aoc.Year2021.Day01.Spec
import Std (List, Nat)

--| Part 1: count the measurements that are larger than the measurement just
--| before them. Each measurement is paired with the next, and the pairs that go
--| deeper are counted.
def increases (measurements: List Nat): Nat := measurements.zipWithNext |> .count (pair => pair.fst < pair.snd)

--| Every run of `size` consecutive measurements, in order: the first `size`
--| measurements from each place in the list, where `size` of them are left.
def slidingWindows (size: Nat) (measurements: List Nat): List (List Nat) :=
  measurements.tails |> .map (.take size) |> .filter (window => window.length == size)

--| Part 2 (with `size` 3): add up each sliding window, and count the sums that
--| are larger than the sum before them.
def windowIncreases (size: Nat) (measurements: List Nat): Nat :=
  slidingWindows size measurements |> .map .sum |> increases
