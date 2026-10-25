-- Day 2 as the puzzle states it, digit by digit: the specification that the
-- proofs (Proofs/) and the brute-force tests (Tests/BruteForce.sw) compare the
-- arithmetic in Day02.sw with. The program itself doesn't use it.

namespace Aoc.Day02.Spec
import Aoc.Common (Range)
import Std (List, Nat)

-- The digits are some block of k digits written n times.
def writtenAs (ds: List Nat) (k: Nat) (n: Nat): Bool := List.concat (List.replicate n (List.take ds k)) == ds

-- Part 1: written twice; part 2: written two or more times.
def doubled (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (k => writtenAs ds k 2)

def repeats (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (k => List.rangeFrom ds.length 2 |> .any (n => writtenAs ds k n))

-- Part 1 as the puzzle states it: in every range walk the ids, keep those whose
-- digits are some block written twice, add them up.
def part1Spec (ranges: List Range): Nat :=
  ranges |> .sumBy (r => r.ids |> .filter doubled |> .sum)

-- The puzzle's method: in every range walk the ids, keep those whose digits
-- are some block written two or more times, add them up.
def part2Spec (ranges: List Range): Nat :=
  ranges |> .sumBy (r => r.ids |> .filter repeats |> .sum)
