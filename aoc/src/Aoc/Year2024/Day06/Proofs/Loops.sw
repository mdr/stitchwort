--| The program's loop test is `Loops`, for sightlines whose next turns are
--| turns of the walk (`Simulates`; proved for the program's sightlines in
--| Proofs/Sightlines.sw): `loopsWithCorrect`.
--
-- A repeated turn is a repeated state, and running out of budget means
-- `stateCount` steps on the map.

namespace Aoc.Year2024.Day06.Proofs
import Aoc.Year2024.Day06 (..)
import Aoc.Common (Direction, Position)
import Aoc.Year2024.Day06.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, Nat, Not, Option, Or, Set, Void)

--| Each next turn `sightlines` finds is where the walk in `lab` is some
--| steps on, and when there is none, the walk leaves.
def Simulates (sightlines: Sightlines) (lab: Lab): Prop :=
  ∀ (guard: Guard) => onMap lab guard.position = True
    → (∀ (next: Guard) => sightlines.nextTurn guard = Some next
      → Exists Nat (steps => (0 < steps) ∧ (walk lab (Some guard) steps = Some next)))
      ∧ (sightlines.nextTurn guard = None → Exists Nat (steps => walk lab (Some guard) steps = None))

theorem afterAdd ∀ (lab: Lab) (now: Nat) (guard: Guard)
    (reached: after lab now = Some guard) (steps: Nat):
    after lab (now + steps) = walk lab (Some guard) steps :=
  rewrite walkAdd lab now (Some lab.startGuard) steps, reached

--| Seen once, at a step no later than `now`.
def SeenBy (lab: Lab) (seen: Set Guard) (now: Nat): Prop :=
  ∀ (guard: Guard) => seen.contains guard = True
    → Exists Nat (earlier => (earlier ≤ now) ∧ (after lab earlier = Some guard))

--| What a set has after an insert: the key, or what it had.
--| A `True` from the loop test means she loops.
theorem loopsFromSound ∀ (lab: Lab) (sightlines: Sightlines)
    (simulates: Simulates sightlines lab)
    (inside: onMap lab lab.start = True)
    (budget: Nat) (guard: Guard) (seen: Set Guard) (now: Nat)
    (reached: after lab now = Some guard)
    (enough: lab.stateCount ≤ now + budget)
    (seenBy: SeenBy lab seen now)
    (says: sightlines.loopsFrom guard seen budget = True):
    Loops lab :=
  match budget with
    | Zero => steps gone =>
      budgetEnough lab inside
        (walkEarlier lab
          (Some lab.startGuard)
          lab.stateCount
          now
          (rewrite reached then Option.someNotNone guard)
          (arithmetic [enough]))
        steps
        gone
    | Succ budget => anySteps gone =>
      let onTheMap := afterOnMap lab inside now guard reached
      match turned: sightlines.nextTurn guard with
        | Some next => Exists.elim (And.left (simulates guard onTheMap) next turned) (steps both =>
          let later: after lab (now + steps) = Some next := Eq.trans (afterAdd lab now guard reached steps) both.right
          (match says with
                | Inl repeated => Exists.elim (seenBy next repeated) (earlier when =>
                  repeatLoops lab earlier
                    (now + steps)
                    (arithmetic [when.left, both.left])
                    (Eq.trans when.right later.flipped)
                    (rewrite later then Option.someNotNone next))
                | Inr rest =>
                  let seenByNext: SeenBy lab (seen.insert next) (now + steps) := guard has =>
                    match Set.containsInsertElim seen next guard has with
                      | Inl isNext =>
                        Witness (now + steps) (Both (Nat.leRefl (now + steps)) (rewrite isNext then later))
                      | Inr wasSeen => Exists.elim (seenBy guard wasSeen) (earlier when =>
                        Witness earlier (Both (arithmetic [when.left]) when.right))
                  loopsFromSound lab sightlines simulates inside budget next
                    (seen.insert next)
                    (now + steps)
                    later
                    (arithmetic [both.left, enough])
                    seenByNext
                    rest) anySteps gone)

--| And when she loops, the test says so.
theorem loopsFromComplete ∀ (lab: Lab) (sightlines: Sightlines)
    (simulates: Simulates sightlines lab)
    (inside: onMap lab lab.start = True)
    (loops: Loops lab)
    (budget: Nat) (guard: Guard) (seen: Set Guard) (now: Nat)
    (reached: after lab now = Some guard):
    sightlines.loopsFrom guard seen budget = True :=
  match budget with
    | Zero => byComputing
    | Succ budget =>
      let onTheMap := afterOnMap lab inside now guard reached
      match turned: sightlines.nextTurn guard with
        | None => Exists.elim (And.right (simulates guard onTheMap) turned) (steps gone =>
          Void.impossible (loops (now + steps) (Eq.trans (afterAdd lab now guard reached steps) gone)))
        | Some next => Exists.elim (And.left (simulates guard onTheMap) next turned) (steps both =>
          Inr
            (loopsFromComplete lab sightlines simulates inside loops budget next
              (seen.insert next)
              (now + steps)
              (Eq.trans (afterAdd lab now guard reached steps) both.right)))

theorem seenStart ∀ (lab: Lab): SeenBy lab (Set.singleton lab.startGuard) 0 := guard has =>
  match Set.containsInsertElim Set.empty lab.startGuard guard has with
    | Inl isStart => Witness 0 (Both byComputing (rewrite isStart))
    | Inr inEmpty => cases

--| The program's loop test decides `Loops`.
theorem loopsWithCorrect ∀ (lab: Lab) (sightlines: Sightlines)
    (simulates: Simulates sightlines lab)
    (inside: onMap lab lab.start = True):
    (lab.loopsWith sightlines = True) ↔ (Loops lab) :=
  {
    forward = says =>
      loopsFromSound lab sightlines simulates inside lab.stateCount lab.startGuard
        (Set.singleton lab.startGuard)
        0
        byComputing
        (Nat.leRefl lab.stateCount)
        (seenStart lab)
        says,
    backward = loops =>
      loopsFromComplete lab sightlines simulates inside loops lab.stateCount lab.startGuard
        (Set.singleton lab.startGuard)
        0
        byComputing
  }
