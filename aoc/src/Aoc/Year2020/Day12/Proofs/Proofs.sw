--| Day 12 proved, about the input text: for every input the parser reads,
--| its lines are the instructions written out, each turn a multiple of 90
--| degrees (Parse.sw), and the answers are the Manhattan distances the
--| spec's ship ends at, moved and turned as the puzzle says (Parts.sw,
--| with the turns in Turns.sw). Both parts answer for every route; the
--| spec's answers are functions of the route, so each names one number.

namespace Aoc.Year2020.Day12.Proofs
import Aoc.Year2020.Day12 (..)
import Aoc.Year2020.Day12 (Spec)
import Std (Eq, Fail, List, Result, Text)

theorem part1Correct ∀ (input: Text) (route: Route) (parsed: Fail.toResult (() => parseRoute input) = Ok route):
    List.All2 Spec.InstructionWritten (input.lines.map Text.toList) route.instructions ∧ Spec.Part1 route.instructions route.shipDistance :=
  Both (parseWritten input route parsed) (part1Rules route)

theorem part2Correct ∀ (input: Text) (route: Route) (parsed: Fail.toResult (() => parseRoute input) = Ok route):
    List.All2 Spec.InstructionWritten (input.lines.map Text.toList) route.instructions ∧ Spec.Part2 route.instructions route.waypointDistance :=
  Both (parseWritten input route parsed) (part2Rules route)

--| Part 1's answer is the spec's, and no other number is.
theorem part1Exactly ∀ (route: Route) (answer: Nat): route.shipDistance = answer ↔ Spec.Part1 route.instructions answer :=
  { forward = same => rewrite <- same in part1Rules route, backward = spec => Eq.trans (part1Rules route) (Eq.sym spec) }

--| Part 2 likewise.
theorem part2Exactly ∀ (route: Route) (answer: Nat): route.waypointDistance = answer ↔ Spec.Part2 route.instructions answer :=
  { forward = same => rewrite <- same in part2Rules route, backward = spec => Eq.trans (part2Rules route) (Eq.sym spec) }
