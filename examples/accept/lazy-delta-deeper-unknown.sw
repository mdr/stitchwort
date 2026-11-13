-- `List.sumCons _ _` for a named sum. `List.sum ?xs` against `weighted (aim
-- + step) rest` is a call with an unknown argument against a call of
-- another definition, but both compute to a `List.foldLeft` stuck on its
-- list, and comparing those solves `?xs`. Lazy delta (SW-1227) leaves such
-- pairs alone: unfolding `weighted` a step and solving `?xs` from
-- `List.sum`'s arguments chose a solution this proof then failed with
-- (2021 Day 2's `aimedDepthCons`).
import Std (Int, List)

def weighted (aim: Int) (steps: List Int): Int :=
  steps
    |> .scanLeft aim (soFar step => soFar + step)
    |> .zipWith steps (at step => at * step)
    |> .sum

theorem weightedCons ∀ (aim: Int) (step: Int) (rest: List Int):
    weighted aim [step, ..rest] = aim * step + weighted (aim + step) rest :=
  List.sumCons _ _
