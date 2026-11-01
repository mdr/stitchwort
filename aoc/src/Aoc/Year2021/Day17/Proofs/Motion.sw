-- How the probe moves: the program's step is the puzzle's, the y position
-- after `n` steps in closed form, and where the probe can't come back from.

namespace Aoc.Year2021.Day17.Proofs
import Aoc.Year2021.Day17 (..)
import Aoc.Year2021.Day17.Spec (..)
import Std (Bool, Eq, Int, Nat, Void)

-- The program's drag, `dx - sign dx`, is the puzzle's.
theorem dragSign: (dx: Int) → dx - Int.sign dx = drag dx
  | OfNat 0 => rfl
  | OfNat (Succ k) => rfl
  | NegSucc k => rfl

theorem stepIsMove (probe: Probe): step probe = move probe := rewrite dragSign probe.dx in rfl

-- The probe after `n` steps of the program, from `velocity`.
def flight (n: Nat) (velocity: Velocity): Probe := Nat.iterate n step (launch velocity)

theorem flightIsAfter (n: Nat) (velocity: Velocity): flight n velocity = after n velocity :=
  Nat.iterateCong step move stepIsMove n (launch velocity)

-- After `n` steps the y velocity is `n` less, and twice the height gained
-- is `n * (2 * dy + 1 - n)`.
theorem dyAfter: (n: Nat) → (probe: Probe) → (Nat.iterate n step probe).dy = probe.dy - n.toInt
  | 0, probe => omega
  | Succ n, probe => omega [dyAfter n (step probe)]

theorem yAfter: (n: Nat) → (probe: Probe) → 2 * (Nat.iterate n step probe).y = 2 * probe.y + n.toInt * (2 * probe.dy + 1 - n.toInt)
  | 0, probe => ring
  | Succ n, probe => ring [yAfter n (step probe)]

-- Drag takes `dx` one toward 0: what `Int.sign` is, by the sign of `dx`.
theorem signCases: (dx: Int) → (Int.sign dx = 1 ∧ 0 < dx) ∨ (Int.sign dx = 0 ∧ dx = 0) ∨ (Int.sign dx = -1 ∧ dx < 0)
  | OfNat 0 => Inr (Inl (Both rfl rfl))
  | OfNat (Succ k) => Inl (Both rfl (omega))
  | NegSucc k => Inr (Inr (Both rfl (omega)))

-- Drag never turns the probe round.
theorem dragKeepsSign (dx: Int): (0 ≤ dx → 0 ≤ dx - Int.sign dx) ∧ (dx ≤ 0 → dx - Int.sign dx ≤ 0) :=
  match signCases dx with
    | Inl (Both s pos) => Both (_ => omega) (_ => omega)
    | Inr (Inl (Both s zero)) => Both (_ => omega) (_ => omega)
    | Inr (Inr (Both s neg)) => Both (_ => omega) (_ => omega)

-- Each way of being past the target lasts.
theorem overshotStays (target: Target) (probe: Probe) (h: overshot target probe = True): overshot target (step probe) = True :=
  omega [(dragKeepsSign probe.dx).left (omega)]

theorem shortStays (target: Target) (probe: Probe) (h: short target probe = True): short target (step probe) = True :=
  omega [(dragKeepsSign probe.dx).right (omega)]

theorem fallenStays (target: Target) (probe: Probe) (h: fallen target probe = True): fallen target (step probe) = True := omega

-- Once past the target, the probe stays past it.
theorem pastStays (target: Target) (probe: Probe) (h: past target probe = True): past target (step probe) = True :=
  Bool.orElim (overshot target probe) (short target probe ∨ fallen target probe) _ h
    (o => Bool.orLeft _ _ (overshotStays target probe o))
    (rest => Bool.orRight _ _ (Bool.orElim (short target probe) (fallen target probe) _ rest
      (s => Bool.orLeft _ _ (shortStays target probe s))
      (f => Bool.orRight _ _ (fallenStays target probe f))))

-- A probe past the target isn't in it.
theorem pastOutside (target: Target) (probe: Probe) (h: past target probe = True): inTarget target probe = False := cases
