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
  ∀ (guard: Guard) => onMap lab guard.position = True →
    (∀ (next: Guard) => sightlines.nextTurn guard = Some next → Exists Nat (steps => (0 < steps) ∧ (walk lab (Some guard) steps = Some next))) ∧ (sightlines.nextTurn guard = None → Exists Nat (steps => walk lab (Some guard) steps = None))

theorem afterAdd (lab: Lab) (now: Nat) (guard: Guard) (reached: after lab now = Some guard) (steps: Nat):
    after lab (now + steps) = walk lab (Some guard) steps :=
  rewrite walkAdd lab now (Some lab.startGuard) steps in rewrite reached in rfl

--| Seen once, at a step no later than `now`.
def SeenBy (lab: Lab) (seen: Set Guard) (now: Nat): Prop :=
  ∀ (guard: Guard) => seen.contains guard = True → Exists Nat (earlier => (earlier ≤ now) ∧ (after lab earlier = Some guard))

--| What a set has after an insert: the key, or what it had.
theorem containsInsertEither (seen: Set Guard) (key: Guard) (guard: Guard) (has: (seen.insert key).contains guard = True):
    (guard = key) ∨ (seen.contains guard = True) :=
  match same: guard == key with
    | True => Inl same.read
    | False => Inr (rewrite Set.containsInsertOther seen key guard same.read at has)

--| A `True` from the loop test means she loops.
theorem loopsFromSound (lab: Lab) (sightlines: Sightlines) (simulates: Simulates sightlines lab) (inside: onMap lab lab.start = True):
    ∀ (budget: Nat) (guard: Guard) (seen: Set Guard) (now: Nat) => after lab now = Some guard → lab.stateCount ≤ now + budget →
      SeenBy lab seen now → sightlines.loopsFrom guard seen budget = True → Loops lab
  | Zero, guard, seen, now, reached, enough, seenBy, says, steps, gone =>
    budgetEnough lab inside (walkEarlier lab (Some lab.startGuard) lab.stateCount now (rewrite reached in Option.someNotNone guard) (omega [enough])) steps gone
  | Succ budget, guard, seen, now, reached, enough, seenBy, says, anySteps, gone =>
    let onTheMap := afterOnMap lab inside now guard reached
    match turned: sightlines.nextTurn guard with
      | Some next =>
        Exists.elim (And.left (simulates guard onTheMap) next turned) (steps both =>
          let later: after lab (now + steps) = Some next := Eq.trans (afterAdd lab now guard reached steps) (And.right both)
          (match says with
            | Inl repeated =>
              Exists.elim (seenBy next repeated) (earlier when =>
                repeatLoops lab earlier (now + steps) (omega [And.left when, And.left both]) (Eq.trans (And.right when) (Eq.sym later))
                  (rewrite later in Option.someNotNone next))
            | Inr rest =>
              let seenByNext: SeenBy lab (seen.insert next) (now + steps) :=
                guard has =>
                  match containsInsertEither seen next guard has with
                    | Inl isNext => Witness (now + steps) (Both (Nat.leRefl (now + steps)) (rewrite isNext in later))
                    | Inr wasSeen =>
                      Exists.elim (seenBy guard wasSeen) (earlier when => Witness earlier (Both (omega [And.left when]) (And.right when)))
              loopsFromSound lab sightlines simulates inside budget next (seen.insert next) (now + steps) later
                (omega [And.left both, enough]) seenByNext rest) anySteps gone)

--| And when she loops, the test says so.
theorem loopsFromComplete (lab: Lab) (sightlines: Sightlines) (simulates: Simulates sightlines lab) (inside: onMap lab lab.start = True)
    (loops: Loops lab) (budget: Nat) (guard: Guard) (seen: Set Guard) (now: Nat) (reached: after lab now = Some guard):
    sightlines.loopsFrom guard seen budget = True :=
  match budget with
    | Zero => rfl
    | Succ budget =>
      let onTheMap := afterOnMap lab inside now guard reached
      match turned: sightlines.nextTurn guard with
        | None =>
          Exists.elim (And.right (simulates guard onTheMap) turned) (steps gone =>
            Void.exfalso (loops (now + steps) (Eq.trans (afterAdd lab now guard reached steps) gone)))
        | Some next =>
          Exists.elim (And.left (simulates guard onTheMap) next turned) (steps both =>
            Inr (loopsFromComplete lab sightlines simulates inside loops budget next (seen.insert next) (now + steps)
              (Eq.trans (afterAdd lab now guard reached steps) (And.right both))))

theorem seenStart (lab: Lab): SeenBy lab (Set.singleton lab.startGuard) 0 :=
  guard has =>
    match containsInsertEither Set.empty lab.startGuard guard has with
      | Inl isStart => Witness 0 (Both rfl (rewrite isStart in rfl))
      | Inr inEmpty => cases

--| The program's loop test decides `Loops`.
theorem loopsWithCorrect (lab: Lab) (sightlines: Sightlines) (simulates: Simulates sightlines lab) (inside: onMap lab lab.start = True):
    (lab.loopsWith sightlines = True) ↔ (Loops lab) := {
  forward = says =>
    loopsFromSound lab sightlines simulates inside lab.stateCount lab.startGuard (Set.singleton lab.startGuard) 0 rfl
      (Nat.leRefl lab.stateCount) (seenStart lab) says,
  backward = loops =>
    loopsFromComplete lab sightlines simulates inside loops lab.stateCount lab.startGuard (Set.singleton lab.startGuard) 0 rfl
}
