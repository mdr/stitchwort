-- Day 19 as the puzzle states it: a design is made by a list of towels whose
-- stripes, end to end, are the design's, and the ways to make it are those
-- lists. The proofs (Proofs/) show the program counts them, for every list
-- of patterns, each with at least one stripe, and every design.

namespace Aoc.Year2024.Day19.Spec
import Aoc.Year2024.Day19 (Design, Onsen, Pattern)
import Std (List, Nat)

-- "You can use any towels you want": every list of at most `count` towels,
-- each with any of the patterns ("for any particular pattern, the staff can
-- get you as many towels with that pattern as you need").
def towelLists (patterns: List Pattern): (count: Nat) → List (List Pattern)
  | Zero => [Nil]
  | Succ count => Cons Nil (patterns.flatMap (first => towelLists patterns count |> .map (Cons first)))

-- "all of the towels' stripes must exactly match the desired design": the
-- lists of towels whose stripes, in order, are the design's. Every towel has
-- a stripe, so none of them has more towels than the design has stripes.
def arrangements (patterns: List Pattern) (design: Design): List (List Pattern) :=
  towelLists patterns design.length |> .filter (towels => towels.concat == design)

-- "Not all designs will be possible with the available towel patterns."
def possible (patterns: List Pattern) (design: Design): Bool := arrangements patterns design != []

-- "all of the different ways ... designs can be made".
def ways (patterns: List Pattern) (design: Design): Nat := (arrangements patterns design).length

-- "How many designs are possible?"
def part1 (onsen: Onsen): Nat := onsen.designs.count (possible onsen.patterns)

-- "What do you get if you add up the number of different ways you could
-- make each design?"
def part2 (onsen: Onsen): Nat := onsen.designs.sumBy (ways onsen.patterns)
