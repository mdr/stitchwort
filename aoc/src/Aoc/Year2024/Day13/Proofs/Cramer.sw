-- Cramer's rule: with a nonzero determinant, `Machine.onlyPresses` finds exactly
-- the presses that win, so there is at most one way to win.

namespace Aoc.Year2024.Day13.Proofs
import Aoc.Year2024.Day13 (..)
import Std (And, Bool, DecEq, Eq, Int, Nat, Option, Void)

-- A win is the two equations, one per axis.
theorem winsEquations (machine: Machine) (aPresses: Nat) (bPresses: Nat) (won: machine.wins aPresses bPresses = True):
    And (aPresses.toInt * machine.buttonA.x + bPresses.toInt * machine.buttonB.x = machine.prize.x)
      (aPresses.toInt * machine.buttonA.y + bPresses.toInt * machine.buttonB.y = machine.prize.y) :=
  Both (DecEq.sound _ _ (Bool.andLeft _ _ won)) (DecEq.sound _ _ (Bool.andRight _ _ won))

-- Eliminating B's presses from the two equations: A's presses times the
-- determinant are what Cramer's rule divides.
theorem aTimesDeterminant (machine: Machine) (aPresses: Nat) (bPresses: Nat) (won: machine.wins aPresses bPresses = True):
    machine.determinant * aPresses.toInt = machine.prize.x * machine.buttonB.y - machine.prize.y * machine.buttonB.x :=
  let equations := winsEquations machine aPresses bPresses won
  let alongX := And.left equations
  let alongY := And.right equations
  ring [machine.buttonB.y * alongX, machine.buttonB.x * alongY]

theorem bTimesDeterminant (machine: Machine) (aPresses: Nat) (bPresses: Nat) (won: machine.wins aPresses bPresses = True):
    machine.determinant * bPresses.toInt = machine.buttonA.x * machine.prize.y - machine.buttonA.y * machine.prize.x :=
  let equations := winsEquations machine aPresses bPresses won
  let alongX := And.left equations
  let alongY := And.right equations
  ring [machine.buttonA.x * alongY, machine.buttonA.y * alongX]

-- Any presses that win are the ones `Machine.onlyPresses` finds.
theorem onlyPressesFinds (machine: Machine) (nonzero: machine.determinant ≠ 0) (aPresses: Nat) (bPresses: Nat)
    (won: machine.wins aPresses bPresses = True): machine.onlyPresses nonzero = Some (aPresses, bPresses) :=
  let aQuotient: (machine.prize.x * machine.buttonB.y - machine.prize.y * machine.buttonB.x) / machine.determinant = aPresses.toInt :=
    rewrite <- aTimesDeterminant machine aPresses bPresses won in Int.mulDivCancel machine.determinant aPresses.toInt [ok := nonzero]
  let bQuotient: (machine.buttonA.x * machine.prize.y - machine.buttonA.y * machine.prize.x) / machine.determinant = bPresses.toInt :=
    rewrite <- bTimesDeterminant machine aPresses bPresses won in Int.mulDivCancel machine.determinant bPresses.toInt [ok := nonzero]
  rewrite aQuotient, bQuotient, won in rfl

-- The presses `Machine.onlyPresses` finds win.
theorem onlyPressesWins (machine: Machine) (nonzero: machine.determinant ≠ 0) (aPresses: Nat) (bPresses: Nat):
    machine.onlyPresses nonzero = Some (aPresses, bPresses) → machine.wins aPresses bPresses = True :=
  found => And.right (Option.filterEqSome _ _ _ found)
