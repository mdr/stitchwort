-- Recursive calls inside a function passed to another (docs/proposals/
-- well-founded-recursion.md, stage 3a): `List.sumBy (d => … weight d …) xs`.
-- The call needs its proof that the measure is smaller, as any recursive
-- call does; the guard `if h: d < n` puts one in scope. The compiler's own
-- proofs go through the function's congruence lemma, `List.sumByCong`
-- (found by name: the function's name and `Cong`), which says the sum is the
-- same for two functions that agree on every argument.
--
--   $ stitchwort run examples/accept/decreasing-lambda.sw
--   weights: 1 1 0 1 -1 1 0 0 -1 1 0
--   chain: 3
--   grow: 13
--   pairs: 3
--   odd parts: 5

import Std (IO, Int, List, Nat, Text)

-- The weight of a repeat count n (AoC 2025 day 2): 1, less the weights of
-- the divisors of n from 2 to n - 1. For n >= 2 this is minus the Moebius
-- function. The guard `d < n` always holds; it's there to show the
-- recursion ends.
def weight (n: Nat): Int
    decreasing n
:=
  1 - (List.rangeFrom (n - 2) 2 |> .sumBy (d => if h: d < n then (if Nat.divides d n then weight d else 0) else 0))

test "weights" := List.map weight (List.rangeFrom 11 2) == [1, 1, 0, 1, -1, 1, 0, 0, -1, 1, 0]

-- A closed value computes, fuel and all.
theorem weightTwelve: weight 12 = 0 := rfl

-- The equation the compiler proves, on an open `n`, with `weight` itself
-- inside the function passed to `sumBy`.
theorem weightStep (n: Nat):
    weight n = 1 - List.sumBy (d => if h: d < n then (if Nat.divides d n then weight d else 0) else 0) (List.rangeFrom (n - 2) 2) :=
  weight.unfold n

-- A fold whose function takes two arguments and uses both: the longest
-- chain of divisors from n down, each dividing the one before.
def chain (n: Nat): Nat
    decreasing n
:=
  1 + List.foldLeft (best d => if h: d < n then (if Nat.leq 2 d && Nat.divides d n then Nat.max best (chain d) else best) else best) 0 (List.range n)

test "chain" := chain 12 == 3 && chain 7 == 1 && chain 1 == 1

-- Recursion in the function and in the fold's starting value, in one call.
def grow (n: Nat): Nat
    decreasing n
:=
  if h: n - 1 < n
  then List.foldLeft (acc d => acc + (if g: d < n then grow d else 0)) (grow (n - 1)) (List.range n)
  else 1

test "grow" := grow 0 == 1 && grow 1 == 2 && grow 2 == 5 && grow 3 == 13

-- The function in a `let`, and a sum inside a sum.
def pairs (n: Nat): Nat
    decreasing n
:=
  let term := (d: Nat) => if h: d < n then 1 + pairs d else 0
  List.sumBy (k => List.sumBy term (List.range k)) (List.range n)

test "pairs" := pairs 0 == 0 && pairs 2 == 1 && pairs 3 == 3

-- A `match` inside the function.
def oddParts (n: Nat): Nat
    decreasing n
:=
  1 + List.sumBy (d => match d with
    | Zero => 0
    | Succ k => if h: Succ k < n then (if Nat.leq n (2 * Succ k) then 0 else oddParts (Succ k)) else 0) (List.range n)

test "odd parts" := oddParts 1 == 1 && oddParts 3 == 2

-- A theorem can recurse inside a function too: strong induction, from the
-- step for every number given the result for the smaller ones.
theorem strong (p: Nat -> Prop) (step: (n: Nat) -> ((d: Nat) -> d < n -> p d) -> p n) (n: Nat): p n
    decreasing n
:=
  step n (d h => strong p step d)

theorem allZeroLe (n: Nat): 0 <= n := strong (k => 0 <= k) (k below => Nat.zeroLe k) n

def main(): {IO} () :=
  IO.print ("weights: " ++ Text.join ' ' (List.map Int.toText (List.map weight (List.rangeFrom 11 2))))
  IO.print ("chain: " ++ Nat.toText (chain 12))
  IO.print ("grow: " ++ Nat.toText (grow 3))
  IO.print ("pairs: " ++ Nat.toText (pairs 3))
  IO.print ("odd parts: " ++ Nat.toText (oddParts 7))
