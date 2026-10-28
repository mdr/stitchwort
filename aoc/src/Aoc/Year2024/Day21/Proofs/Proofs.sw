-- Day 21 proved, for every code and number of robots: the program's length
-- is achieved, by presses that type the code (`lengthAchieved`, from
-- Presses.sw and Typing.sw). That no shorter presses type it is `Optimal`;
-- with it, the program's length is the spec's shortest
-- (`shortestIfOptimal`) and both parts are the puzzle's answers
-- (`part1Correct`, `part2Correct`). `Optimal` follows from a walk fact on
-- each keypad (Lower.sw), proved where you press the keys yourself
-- (Direct.sw), so with no robots on directional keypads; with robots it is
-- not proved. The parser isn't proved.

namespace Aoc.Year2024.Day21.Proofs
import Aoc.Year2024.Day21 (..)
import Aoc.Year2024.Day21.Spec (..)
import Std (And, Exists, List, Nat)

-- Some presses as many as the program's length type the code.
theorem lengthAchieved (robots: Nat) (code: Code):
    Exists (List DirectionKey) (presses => And (Types robots code presses) (presses.length = (robotCosts robots).shortestLength code)) :=
  Witness (pressesFor robots code) (Both (pressesForTypes robots code) (pressesForLength robots code))

-- No presses shorter than the program's length type the code. Proved for
-- no robots (`shortestWithoutRobots`); for more, it needs `CheapestWalks`
-- at their levels (`optimalIfCheapestWalks`).
def Optimal (robots: Nat): Prop :=
  (code: Code) → (presses: List DirectionKey) → Types robots code presses → (robotCosts robots).shortestLength code ≤ presses.length

theorem shortestIfOptimal (robots: Nat) (optimal: Optimal robots) (code: Code): Shortest robots code ((robotCosts robots).shortestLength code) :=
  Both (lengthAchieved robots code) (presses types => optimal code presses types)

theorem complexitiesAnswer (robots: Nat) (optimal: Optimal robots) (codes: List Code): Answer robots codes (complexities robots codes) :=
  Witness (robotCosts robots).shortestLength (Both (code member => shortestIfOptimal robots optimal code) rfl)

theorem part1Correct (optimal: Optimal 2) (codes: List Code): Answer 2 codes (solvePart1 codes) := complexitiesAnswer 2 optimal codes

theorem part2Correct (optimal: Optimal 25) (codes: List Code): Answer 25 codes (solvePart2 codes) := complexitiesAnswer 25 optimal codes
