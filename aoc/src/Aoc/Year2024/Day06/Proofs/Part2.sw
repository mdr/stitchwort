-- Part 2 proved: a new obstruction off the guard's route never traps her
-- (`offRouteFree`), the route's positions are on the map and free except the
-- start (`routeSettled`), so the program's set of trap positions is the
-- spec's (`part2Correct`).

namespace Aoc.Year2024.Day06.Proofs
import Aoc.Year2024.Day06 (..)
import Aoc.Year2024.Day06.Spec (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Iff, List, Map, Nat, Not, Option, Or, Set, Void)

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

-- A position is its row and column.
theorem positionEta: (position: Position) → ({ row = position.row, column = position.column }: Position) = position
  | { row, column } => rfl

-- Every position on the map is in `positions`, and only those.
theorem positionsOnMap (lab: Lab) (position: Position) (inside: onMap lab position = True):
    (positions lab).any (other => Map.Spec.sameKey position other) = True :=
  let inRow: position ∈ (List.range lab.width |> .map (column => ({ row = position.row, column }: Position))) :=
    rewrite positionEta position at List.memMap (List.range lab.width) position.column (List.memRangeFromIntro position.column lab.width 0 omega (omega [inside]))
      (column => ({ row = position.row, column }: Position))
  let member: position ∈ positions lab :=
    List.memFlatMapIntro (row => List.range lab.width |> .map (column => ({ row, column }: Position))) position.row position
      (List.range lab.height) (List.memRangeFromIntro position.row lab.height 0 omega (omega [inside])) inRow
  List.anyOfMem (positions lab) (other => Map.Spec.sameKey position other) position
    (rewrite Map.Spec.sameKeyDecide position position in DecEq.refl position) member

theorem positionsOnlyOnMap (lab: Lab) (position: Position) (has: (positions lab).any (other => Map.Spec.sameKey position other) = True):
    onMap lab position = True :=
  List.anyTrueElim (positions lab) (other => Map.Spec.sameKey position other) (onMap lab position = True) has (other member same =>
    rewrite Map.Spec.sameKeySound position other same in
    List.anyElim (row => other ∈ (List.range lab.width |> .map (column => ({ row, column }: Position)))) (onMap lab other = True)
      (List.range lab.height)
      (List.memFlatMapElim (row => List.range lab.width |> .map (column => ({ row, column }: Position))) other (List.range lab.height) member)
      (row rowMember inRow =>
        List.anyElim (column => ({ row, column }: Position) = other) (onMap lab other = True) (List.range lab.width)
          (List.memMapAny (List.range lab.width) (column => ({ row, column }: Position)) other inRow)
          (column columnMember built =>
            let rowSmall := List.memRangeFrom row lab.height 0 rowMember
            let columnSmall := List.memRangeFrom column lab.width 0 columnMember
            rewrite <- built in omega [rowSmall, columnSmall])))

theorem positionsHas (lab: Lab) (position: Position):
    Set.contains (Set.fromList (positions lab)) position = onMap lab position :=
  rewrite Set.containsFromList position (positions lab) in
  match inside: onMap lab position with
    | True => positionsOnMap lab position inside
    | False =>
      match has: (positions lab).any (other => Map.Spec.sameKey position other) with
        | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym inside) (positionsOnlyOnMap lab position has)))
        | False => rfl

-- Two Bools true together are equal.
theorem boolOfIff (one: Bool) (other: Bool) (same: Iff (one = True) (other = True)): one = other :=
  match isOne: one, isOther: other with
    | True, True => rfl
    | False, False => rfl
    | True, False => Void.exfalso (Bool.falseNotTrue (same.forward rfl))
    | False, True => Void.exfalso (Bool.falseNotTrue (same.backward rfl))

-- The start is settled.
theorem startSettled (lab: Lab) (inside: onMap lab lab.start = True): settledAt lab lab.start = True :=
  rewrite inside, DecEq.refl lab.start in rfl

-- What the program's filter keeps.
def keeps (lab: Lab) (sightlines: Sightlines) (position: Position): Bool :=
  position != lab.start && lab.loopsWith (sightlines.add position)

-- What the spec's filter keeps.
def trapsAt (lab: Lab) (trapped: Position → Bool) (position: Position): Bool :=
  position != lab.start && !lab.obstructions.contains position && trapped position

-- The Boolean shape of `keepsTrapsAt` on the route: the start is out on
-- both sides, and elsewhere a route position is free.
theorem shapeOnRoute [p: Prop] (atStart: Decidable p) (blocked: Bool) (onTheMap: Bool) (loops: Bool) (trap: Bool) (mapped: onTheMap = True)
    (settled: (Decidable.toBool atStart || !blocked) = True) (same: loops = trap):
    (Decidable.toBool (Decidable.not atStart) && loops) = (onTheMap && (Decidable.toBool (Decidable.not atStart) && !blocked && trap)) :=
  rewrite same in cases

-- Off the route nothing is kept.
theorem shapeOffRoute (onTheMap: Bool) (notStart: Bool) (free: Bool): False = (onTheMap && (notStart && free && False)) := cases

-- The program keeps a position of the route exactly when the spec keeps it.
theorem keepsTrapsAt (lab: Lab) (inside: onMap lab lab.start = True) (steps: Nat) (gone: after lab steps = None)
    (trapped: Position → Bool) (decides: Decides lab trapped)
    (simulates: (blocker: Position) → onMap lab blocker = True →
      Simulates ((Sightlines.of lab.obstructions).add blocker) (lab.withObstruction blocker))
    (position: Position):
    (onRoute lab (Some lab.startGuard) steps position && keeps lab (Sightlines.of lab.obstructions) position)
      = (onMap lab position && trapsAt lab trapped position) :=
  match onIt: onRoute lab (Some lab.startGuard) steps position with
    | True =>
      let settled := routeSettled lab position steps (Some lab.startGuard) (startSettled lab inside) onIt
      let onTheMap: onMap lab position = True := Bool.andLeft _ _ settled
      let loopsSame: lab.loopsWith ((Sightlines.of lab.obstructions).add position) = trapped position :=
        boolOfIff _ _
          (Iff.trans (loopsWithCorrect (lab.withObstruction position) ((Sightlines.of lab.obstructions).add position) (simulates position onTheMap) inside)
            (Iff.symm (decides position)))
      shapeOnRoute _ _ _ _ _ onTheMap (Bool.andRight _ _ settled) loopsSame
    | False =>
      let free := offRouteFree lab inside steps gone position onIt
      let notTrapped: trapped position = False :=
        match isTrapped: trapped position with
          | True => Void.exfalso (free ((decides position).forward isTrapped))
          | False => rfl
      rewrite notTrapped in shapeOffRoute _ _ _

-- Two filtered sets are equal when each keeps what the other does.
theorem filterSame (visited: Set Position) (keep: Position → Bool) (area: Set Position) (spec: Position → Bool)
    (each: (position: Position) → (visited.contains position && keep position) = (area.contains position && spec position)):
    visited.filter keep = area.filter spec :=
  Set.ext _ _ (position =>
    rewrite Set.containsFilter visited position keep, Set.containsFilter area position spec in each position)

-- The positions the program keeps from the route are the spec's trap
-- positions.
theorem trapSetsSame (lab: Lab) (inside: onMap lab lab.start = True) (steps: Nat) (gone: after lab steps = None)
    (trapped: Position → Bool) (decides: Decides lab trapped)
    (simulates: (blocker: Position) → onMap lab blocker = True →
      Simulates ((Sightlines.of lab.obstructions).add blocker) (lab.withObstruction blocker)):
    (Set.fromList (route lab (Some lab.startGuard) steps)).filter (keeps lab (Sightlines.of lab.obstructions)) = trapPositions lab trapped :=
  filterSame (Set.fromList (route lab (Some lab.startGuard) steps)) (keeps lab (Sightlines.of lab.obstructions))
    (Set.fromList (positions lab)) (trapsAt lab trapped)
    (position =>
      Eq.trans
        (Eq.cong (has => has && keeps lab (Sightlines.of lab.obstructions) position)
          (Set.containsFromList position (route lab (Some lab.startGuard) steps)))
        (Eq.trans (keepsTrapsAt lab inside steps gone trapped decides simulates position)
          (Eq.cong (has => has && trapsAt lab trapped position) (Eq.sym (positionsHas lab position)))))

-- Part 2: for a guard who starts on the map and leaves, in a lab whose
-- obstructions are on the map, the program counts the spec's trap
-- positions.
theorem part2Correct (lab: Lab) (inside: onMap lab lab.start = True)
    (obstructionsInside: (position: Position) → lab.obstructions.contains position = True → onMap lab position = True)
    (steps: Nat) (gone: after lab steps = None) (trapped: Position → Bool) (decides: Decides lab trapped):
    solvePart2 lab = Some (trapPositions lab trapped).size :=
  let simulates := programSimulates lab obstructionsInside
  let counted: Option.map (Some (Set.fromList (route lab (Some lab.startGuard) steps)))
      (visited => (visited.filter (keeps lab (Sightlines.of lab.obstructions))).size) = Some (trapPositions lab trapped).size :=
    Eq.cong (set => Some (Set.size set)) (trapSetsSame lab inside steps gone trapped decides simulates)
  Eq.trans (Eq.cong (patrolled => Option.map patrolled (visited => (visited.filter (keeps lab (Sightlines.of lab.obstructions))).size))
    (patrolRoute lab inside steps gone)) counted

-- A guard who loops has no patrol.
theorem patrolLoops (lab: Lab) (loops: Loops lab): lab.patrol = None :=
  match patrolled: lab.patrol with
    | None => rfl
    | Some found => Void.exfalso (loops lab.stateCount (patrolFromGone lab lab.stateCount lab.startGuard Set.empty found patrolled))

-- And part 2 gives no answer when she loops without a new obstruction.
theorem part2Loops (lab: Lab) (loops: Loops lab): solvePart2 lab = None :=
  Eq.cong (patrolled => Option.map patrolled (visited => (visited.filter (keeps lab (Sightlines.of lab.obstructions))).size)) (patrolLoops lab loops)
