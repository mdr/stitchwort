--| The highest point: a probe launched at `dy` never goes above `peak`
--| (1 + 2 + … + dy, or 0 when it isn't thrown up), and reaches it after
--| `dy` steps.

namespace Aoc.Year2021.Day17.Proofs
import Aoc.Year2021.Day17 (..)
import Std (Bool, Eq, Exists, Int, Nat, Void)

--| Twice 1 + 2 + … + k is k * (k + 1).
theorem triangleDouble ∀ (k: Nat): 2 * (triangle k).toInt = k.toInt * (k.toInt + 1) := match k with
  | 0 => byComputing
  | Succ k => algebra [triangleDouble k]

--| Twice the height after `n` steps (`yFlight`) is at most twice the peak.
theorem twiceBelowPeak ∀ (dy: Int) (n: Nat): n.toInt * (2 * dy + 1 - n.toInt) ≤ 2 * (triangle dy.toNat).toInt :=
  match dy with
    | OfNat k =>
      let gap: k.toInt * (k.toInt + 1) - n.toInt * (2 * k.toInt + 1 - n.toInt)
        = (k.toInt - n.toInt) * (k.toInt - n.toInt + 1) :=
        algebra
      arithmetic [triangleDouble k, Int.mulNonnegSucc (k.toInt - n.toInt)]
    | NegSucc k =>
      let flipped: n.toInt * (2 * NegSucc k + 1 - n.toInt) = -(n.toInt * (n.toInt - 2 * NegSucc k - 1)) := algebra
      arithmetic [Int.mulNonneg n.toInt (n.toInt - 2 * NegSucc k - 1) (arithmetic) (arithmetic)]

--| ... and equal to it after `dy` steps (none, when `dy` isn't positive).
theorem twicePeakAt ∀ (dy: Int): dy.toNat.toInt * (2 * dy + 1 - dy.toNat.toInt) = 2 * (triangle dy.toNat).toInt :=
  match dy with
    | OfNat k => algebra [triangleDouble k]
    | NegSucc k => byComputing

theorem peakAbove ∀ (velocity: Velocity) (n: Nat): (flight n velocity).position.y ≤ (peak velocity).toInt :=
  arithmetic [yFlight velocity n, twiceBelowPeak velocity.y n]

theorem peakReached ∀ (velocity: Velocity): (flight velocity.y.toNat velocity).position.y = (peak velocity).toInt :=
  arithmetic [yFlight velocity (Int.toNat velocity.y), twicePeakAt velocity.y]
