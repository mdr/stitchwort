-- Searching the numbers in order with `List.find`: what it finds is the
-- first that passes, and when it finds nothing, none in the range passes.

namespace Aoc.Year2024.Day14.Proofs
import Std (DecEq, Eq, List, Nat, Option, Void)

-- No number before the one found passes.
theorem findRangeFirst (passes: Nat → Bool): (count: Nat) → (start: Nat) → (found: Nat) →
    (List.rangeFrom count start).find passes = Some found → (earlier: Nat) → start ≤ earlier → earlier < found → passes earlier = False
  | Zero, start, found, h, earlier, low, high => Void.exfalso (Option.noneNotSome found h)
  | Succ count, start, found, h, earlier, low, high =>
    match c: passes start with
      | True => Void.exfalso (omega [Option.someInjective start found h])
      | False =>
        match e: earlier == start with
          | True => rewrite DecEq.sound earlier start e in c
          | False => findRangeFirst passes count (Succ start) found h earlier omega high

-- What is found passes, is in the range, and is the first that passes.
theorem findRangeSome (passes: Nat → Bool) (count: Nat) (found: Nat) (h: (List.range count).find passes = Some found):
    And (passes found = True) (And (found < count) ((earlier: Nat) → earlier < found → passes earlier = False)) :=
  match List.findSome (List.range count) passes found h with
    | Both foundPasses member =>
      Both foundPasses (Both (And.right (List.memRangeFrom found count 0 member)) (earlier before => findRangeFirst passes count 0 found h earlier omega before))

-- Finding nothing means nothing in the range passes.
theorem findRangeNone (passes: Nat → Bool) (count: Nat) (h: (List.range count).find passes = None) (seconds: Nat) (below: seconds < count):
    passes seconds = False :=
  match c: passes seconds with
    | True => Void.exfalso (List.findNoneNotMem (List.range count) passes seconds c (List.memRangeFromIntro seconds count 0 omega omega) h)
    | False => rfl
