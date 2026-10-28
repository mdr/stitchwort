-- Day 21 proved, for every code and number of robots: the program's length
-- is achieved, by presses that type the code (`lengthAchieved`, from
-- Presses.sw and Typing.sw). That no shorter presses type it is stated as
-- `Optimal` and not proved; with it, the program's length is the spec's
-- shortest (`shortestIfOptimal`) and both parts are the puzzle's answers
-- (`part1Correct`, `part2Correct`). The parser isn't proved.

namespace Aoc.Year2024.Day21.Proofs
import Aoc.Year2024.Day21 (..)
import Aoc.Year2024.Day21.Spec (..)
import Std (And, Exists, List, Nat)

-- Some presses as many as the program's length type the code.
theorem lengthAchieved (robots: Nat) (code: Code):
    Exists (List DirectionKey) (presses => And (Types robots code presses) (presses.length = shortestLength (robotCosts robots) code)) :=
  Witness (pressesFor robots code) (Both (pressesForTypes robots code) (pressesForLength robots code))

-- Not proved: no presses shorter than the program's length type the code.
-- It would need every walk of an arm between two keys, typed through the
-- keypads before it, to cost at least the cheaper of the program's two
-- routes (see the notes).
def Optimal (robots: Nat): Prop :=
  (code: Code) → (presses: List DirectionKey) → Types robots code presses → shortestLength (robotCosts robots) code ≤ presses.length

theorem shortestIfOptimal (robots: Nat) (optimal: Optimal robots) (code: Code): Shortest robots code (shortestLength (robotCosts robots) code) :=
  Both (lengthAchieved robots code) (presses types => optimal code presses types)

theorem complexitiesAnswer (robots: Nat) (optimal: Optimal robots) (codes: List Code): Answer robots codes (complexities robots codes) :=
  Witness (shortestLength (robotCosts robots)) (Both (code member => shortestIfOptimal robots optimal code) rfl)

theorem part1Correct (optimal: Optimal 2) (codes: List Code): Answer 2 codes (solvePart1 codes) := complexitiesAnswer 2 optimal codes

theorem part2Correct (optimal: Optimal 25) (codes: List Code): Answer 25 codes (solvePart2 codes) := complexitiesAnswer 25 optimal codes
