-- `List.attach` (docs/proposals/well-founded-recursion.md, stage 3b): each
-- element of a list with the proof that it's in the list, so a recursive
-- call inside the function passed to `sumBy` can say why its argument is
-- smaller without a guard. `e.value` is the element and `e.isIn` the proof;
-- `List.memRangeFrom` turns the proof into bounds. The compiler's own proofs
-- go through `List.sumByCong`, as for any list.
--
--   $ stitchwort run examples/accept/decreasing-attach.sw
--   weights: 1 1 0 1 -1 1 0 0 -1 1 0
--   chains: 1 2 2 4 2 6
--   sum: 6

import Std (And, Eq, IO, Int, List, Nat, Text)

-- A number in the run `2 .. n - 1` is below n (even when n < 2, where the
-- run is empty).
theorem belowOfRun (d: Nat) (n: Nat) (h: List.Mem d (List.rangeFrom (n - 2) 2)): d < n :=
  match List.memRangeFrom d (n - 2) 2 h with
    | Both lo hi => Nat.ltOfRunSub 2 d n lo hi

-- The weight of a repeat count n (AoC 2025 day 2), as in
-- decreasing-lambda.sw but with no guard: the proof that `d.value < n` comes
-- from `d.isIn`.
def weight (n: Nat): Int
    decreasing n
:=
  1 - (List.rangeFrom (n - 2) 2 |> .attach |> .sumBy (d =>
    if Nat.divides d.value n then weight d.value [decreasing := belowOfRun d.value n d.isIn] else 0))

test "weights" := List.map weight (List.rangeFrom 11 2) == [1, 1, 0, 1, -1, 1, 0, 0, -1, 1, 0]

theorem weightTwelve: weight 12 = 0 := rfl

-- The equation the compiler proves, on an open `n`: the congruence lemma
-- `List.sumByCong` works on the attached list as on any other.
theorem weightStep (n: Nat):
    weight n = 1 - List.sumBy (d => if Nat.divides d.value n then weight d.value else 0) (List.attach (List.rangeFrom (n - 2) 2)) :=
  weight.unfold n

-- Once the call is made, the proofs can go: a sum over the attached list
-- that only looks at the values is the sum over the list.
theorem weightPlain (n: Nat):
    weight n = 1 - List.sumBy (d => if Nat.divides d n then weight d else 0) (List.rangeFrom (n - 2) 2) :=
  Eq.trans (weight.unfold n)
    (Eq.cong (Int.sub 1) (List.sumByAttach (d => if Nat.divides d n then weight d else 0) (List.rangeFrom (n - 2) 2)))

-- A record pattern in the lambda: the number of chains n, d1, d2, …, each a
-- divisor of the one before and smaller than it. `isIn` is named in the
-- pattern; `List.memRangeFrom` gives `d < 0 + n`, which is `d < n`.
def chains (n: Nat): Nat
    decreasing n
:=
  1 + (List.range n |> .attach |> .sumBy (({ value = d, isIn }) =>
    if Nat.leq 1 d && Nat.divides d n then chains d [decreasing := And.right (List.memRangeFrom d n 0 isIn)] else 0))

test "chains" := List.map chains [1, 2, 3, 4, 5, 6] == [1, 2, 2, 4, 2, 6]

-- The membership facts on their own.
theorem fourInRange: List.Mem 4 (List.between 2 6) := Inr (Inr (Inl rfl))

theorem betweenBounds (x: Nat) (h: List.Mem x (List.between 2 6)): And (2 <= x) (x <= 6) := List.memBetween h

test "sum" := List.sumBy (e => e.value) (List.attach [1, 2, 3]) == 6

def main(): {IO} () :=
  IO.print ("weights: " ++ Text.join ' ' (List.map Int.toText (List.map weight (List.rangeFrom 11 2))))
  IO.print ("chains: " ++ Text.join ' ' (List.map Nat.toText (List.map chains [1, 2, 3, 4, 5, 6])))
  IO.print ("sum: " ++ Nat.toText (List.sumBy (e => e.value) (List.attach [1, 2, 3])))
