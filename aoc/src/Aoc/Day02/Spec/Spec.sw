-- Day 2 as the puzzle states it, digit by digit: the specification that the
-- proofs (Proofs/) and the brute-force tests (Tests/BruteForce.sw) compare the
-- arithmetic in Day02.sw with. The program itself doesn't use it.

namespace Aoc.Day02.Spec
import Std (List, Nat)

-- The digits are some block of k digits written n times.
def writtenAs (ds: List Nat) (k: Nat) (n: Nat): Bool := List.concat (List.replicate n (List.take k ds)) == ds

-- Part 1: written twice; part 2: written two or more times.
def doubled (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (k => writtenAs ds k 2)

def repeats (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (k => List.rangeFrom ds.length 2 |> .any (n => writtenAs ds k n))
