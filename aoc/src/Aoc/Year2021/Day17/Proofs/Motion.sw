--| How the probe moves: the program's step is the puzzle's, the y position
--| after `n` steps in closed form, and where the probe can't come back from.

namespace Aoc.Year2021.Day17.Proofs
import Aoc.Year2021.Day17 (..)
import Aoc.Year2021.Day17.Spec (..)
import Std (Bool, Eq, Int, Nat, Void)

--| The program's drag, `dx - sign dx`, is the puzzle's.
theorem dragSign ∀ (dx: Int): dx - dx.sign = drag dx := match dx with
  | OfNat 0 => rfl
  | OfNat (Succ k) => rfl
  | NegSucc k => rfl

theorem stepIsMove ∀ (probe: Probe): step probe = move probe := rewrite dragSign probe.velocity.x in rfl

--| The probe after `n` steps of the program, from `velocity`.
def flight (n: Nat) (velocity: Velocity): Probe := Nat.iterate n step (launch velocity)

theorem flightIsAfter ∀ (n: Nat) (velocity: Velocity): flight n velocity = after n velocity :=
  Nat.iterateCong n step move (launch velocity) stepIsMove

--| After `n` steps the y velocity is `n` less, and twice the height gained
--| is `n * (2 * dy + 1 - n)`.
theorem dyAfter ∀ (n: Nat) (probe: Probe): (Nat.iterate n step probe).velocity.y = probe.velocity.y - n.toInt :=
  match n with
    | 0 => omega
    | Succ n => omega [dyAfter n (step probe)]

theorem yAfter ∀ (n: Nat) (probe: Probe): 2 * (Nat.iterate n step probe).position.y = 2 * probe.position.y + n.toInt * (2 * probe.velocity.y + 1 - n.toInt) :=
  match n with
    | 0 => ring
    | Succ n => ring [yAfter n (step probe)]

--| Once past the target, the probe stays past it.
theorem pastStays ∀ (target: Target) (probe: Probe) (h: past target probe = True): past target (step probe) = True :=
  omega [Int.signCases probe.velocity.x]

--| A probe past the target isn't in it.
theorem pastOutside ∀ (target: Target) (probe: Probe) (h: past target probe = True): inTarget target probe = False := cases
