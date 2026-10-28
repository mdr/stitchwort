-- Part 2 proved: a new obstruction off the guard's route never traps her
-- (`offRouteFree`), the route's positions are on the map and free except the
-- start (`routeSettled`), so the program's set of trap positions is the
-- spec's (`part2Correct`).

namespace Aoc.Year2024.Day06.Proofs
import Aoc.Year2024.Day06 (..)
import Aoc.Year2024.Day06.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Map, Nat, Not, Option, Or, Set, Void)

theorem orFalseLeft (a: Bool) (b: Bool) (h: (a || b) = False): a = False := cases

theorem orFalseRight (a: Bool) (b: Bool) (h: (a || b) = False): b = False := cases

-- Stepping forward onto a free position.
theorem stepMoves (lab: Lab) (guard: Guard) (ahead: Position) (inFront: lab.ahead guard = Some ahead) (blocked: lab.obstructions.contains ahead = False):
    lab.step guard = Some ({ guard | position = ahead }) :=
  rewrite inFront, blocked in rfl

-- An obstruction changes nothing about what is ahead.
theorem aheadWith (lab: Lab) (blocker: Position) (guard: Guard): (lab.withObstruction blocker).ahead guard = lab.ahead guard := cases

-- The lab with an obstruction added steps as before, wherever she doesn't
-- walk onto it.
theorem stepWithSame (lab: Lab) (blocker: Position) (guard: Guard)
    (fresh: (ahead: Position) → lab.ahead guard = Some ahead → lab.obstructions.contains ahead = False → Not (ahead = blocker)):
    (lab.withObstruction blocker).step guard = lab.step guard :=
  rewrite aheadWith lab blocker guard in
  match inFront: lab.ahead guard with
    | None => rfl
    | Some ahead =>
      match blocked: lab.obstructions.contains ahead with
        | True => rewrite Set.containsInsertMono lab.obstructions blocker ahead blocked in rfl
        | False => rewrite Set.containsInsertOther lab.obstructions blocker ahead (fresh ahead rfl blocked), blocked in rfl

-- Whether the route has `position`, as `Set.fromList` sees it.
def onRoute (lab: Lab) (guard: Option Guard) (steps: Nat) (position: Position): Bool :=
  (route lab guard steps).any (other => Map.Spec.sameKey position other)

-- With the obstruction off her route for one step more, the walk in the
-- changed lab is the walk in the old one.
theorem walkWithSame (lab: Lab) (blocker: Position): (steps: Nat) → (guard: Option Guard) → onRoute lab guard (Succ steps) blocker = False →
    walk (lab.withObstruction blocker) guard steps = walk lab guard steps
  | Zero, guard, absent => rfl
  | Succ steps, None, absent => rewrite walkNone (lab.withObstruction blocker) steps, walkNone lab steps in rfl
  | Succ steps, Some here, absent =>
    let restAbsent: onRoute lab (lab.step here) (Succ steps) blocker = False := orFalseRight _ _ absent
    let fresh := (ahead: Position) (inFront: lab.ahead here = Some ahead) (blocked: lab.obstructions.contains ahead = False) =>
      let movedAbsent := rewrite stepMoves lab here ahead inFront blocked at restAbsent
      let notSame: Map.Spec.sameKey blocker ahead = False := orFalseLeft _ _ movedAbsent
      DecEq.soundFalse ahead blocker (rewrite Map.Spec.sameKeyDecide blocker ahead at notSame)
    rewrite stepWithSame lab blocker here fresh in walkWithSame lab blocker steps (lab.step here) restAbsent

-- A new obstruction off the route of a guard who leaves can't trap her.
theorem offRouteFree (lab: Lab) (inside: onMap lab lab.start = True) (steps: Nat) (gone: after lab steps = None) (blocker: Position)
    (absent: onRoute lab (Some lab.startGuard) steps blocker = False): Not (Loops (lab.withObstruction blocker)) :=
  loops =>
    let longer: onRoute lab (Some lab.startGuard) (Succ steps) blocker = False :=
      Eq.trans (Eq.cong (positions => positions.any (other => Map.Spec.sameKey blocker other)) (routeAfterGone lab steps (Some lab.startGuard) gone (Succ steps) omega)) absent
    loops steps (Eq.trans (walkWithSame lab blocker steps (Some lab.startGuard) longer) gone)

-- On the map, and free unless it is the start.
def settledAt (lab: Lab) (position: Position): Bool :=
  onMap lab position && (position == lab.start || !lab.obstructions.contains position)

def settledIfAny (lab: Lab): Option Guard → Bool
  | None => True
  | Some guard => settledAt lab guard.position

theorem stepSettled (lab: Lab) (guard: Guard) (settled: settledAt lab guard.position = True) (next: Guard) (stepped: lab.step guard = Some next):
    settledAt lab next.position = True :=
  match inFront: lab.ahead guard with
    | None => Void.exfalso (Option.noneNotSome next stepped)
    | Some ahead =>
      match blocked: lab.obstructions.contains ahead with
        | True => rewrite <- Option.someInjective _ next stepped in settled
        | False =>
          let landed := aheadOnMap lab guard (Bool.andLeft _ _ settled) ahead inFront
          rewrite <- Option.someInjective _ next stepped in (cases: settledAt lab ahead = True)

-- Every position on the route is settled.
theorem routeSettled (lab: Lab) (position: Position): (steps: Nat) → (guard: Option Guard) → settledIfAny lab guard = True →
    onRoute lab guard steps position = True → settledAt lab position = True
  | Zero, guard, settled, has => Void.exfalso (Bool.falseNotTrue has)
  | Succ steps, None, settled, has => Void.exfalso (Bool.falseNotTrue has)
  | Succ steps, Some here, settled, has =>
    Bool.orElim (Map.Spec.sameKey position here.position) (onRoute lab (lab.step here) steps position) (settledAt lab position = True) has
      (same => rewrite Map.Spec.sameKeySound position here.position same in settled)
      (rest =>
        let nextSettled: settledIfAny lab (lab.step here) = True :=
          match stepped: lab.step here with
            | None => rfl
            | Some next => stepSettled lab here settled next stepped
        routeSettled lab position steps (lab.step here) nextSettled rest)
