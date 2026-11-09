--| The program's bounded simulation decides whether the probe is in the
--| target within its number of steps, though it stops early once the probe
--| is past it.

namespace Aoc.Year2021.Day17.Proofs
import Aoc.Year2021.Day17 (..)
import Std (Bool, Eq, Exists, Nat, Void)

--| A probe past the target is never in it again.
theorem pastNever (target: Target) (probe: Probe) (h: past target probe = True) (n: Nat): inTarget target (Nat.iterate n step probe) = False :=
  pastOutside target _ (Nat.iterateKeeps step (q => past target q = True) (pastStays target) n probe h)

--| What `hitsWithin` finds is there.
theorem hitsWithinSound (target: Target): ∀ (steps: Nat) (probe: Probe) => hitsWithin target steps probe = True →
    ∃ (n: Nat) => n ≤ steps ∧ inTarget target (Nat.iterate n step probe) = True
  | 0, probe, h => Witness 0 (Both (omega) h)
  | Succ steps, probe, h =>
    match i: inTarget target probe with
      | True => Witness 0 (Both (omega) i)
      | False =>
        match q: past target probe with
          | True => Void.exfalso (Bool.falseNotTrue h)
          | False =>
            match hitsWithinSound target steps (step probe) h with
              | Witness n (Both early inside) => Witness (Succ n) (Both (omega) inside)

--| And it finds every hit within its steps.
theorem hitsWithinComplete (target: Target): ∀ (steps n: Nat) (probe: Probe) => n ≤ steps → inTarget target (Nat.iterate n step probe) = True →
    hitsWithin target steps probe = True
  | 0, 0, probe, early, h => h
  | Succ steps, 0, probe, early, h => rewrite h in rfl
  | 0, Succ n, probe, early, h => omega
  | Succ steps, Succ n, probe, early, h =>
    match i: inTarget target probe with
      | True => rfl
      | False =>
        match q: past target probe with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (pastNever target (step probe) (pastStays target probe q) n)) h))
          | False => hitsWithinComplete target steps n (step probe) (omega) h
