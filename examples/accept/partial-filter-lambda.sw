-- The same with a lambda, and the other list functions whose callbacks may
-- be partial: each is partial when its callback is.
import Std (List, Nat, Option)

def collatzSteps (n: Nat): {Partial} Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

def quickOnes (numbers: List Nat): {Partial} (List Nat) := numbers.filter (n => Nat.leq (collatzSteps n) 9)

def totalSteps (numbers: List Nat): {Partial} Nat := List.sumBy numbers collatzSteps

def anySlow (numbers: List Nat): {Partial} Bool := numbers.any (n => Nat.leq 101 (collatzSteps n))

def firstSlow (numbers: List Nat): {Partial} (Option Nat) := numbers.find (n => Nat.leq 101 (collatzSteps n))

def quickPrefix (numbers: List Nat): {Partial} (List Nat) := numbers.takeWhile (n => Nat.leq (collatzSteps n) 9)

test "filter with a partial lambda" := quickOnes [3, 7, 27, 8] == [3, 8]
test "sumBy" := totalSteps [3, 7, 27] == 134
test "any" := anySlow [3, 27] ∧ ¬anySlow [3, 7]
test "find" := firstSlow [3, 27, 7] == Some 27
test "takeWhile" := quickPrefix [3, 8, 7, 1] == [3, 8]
