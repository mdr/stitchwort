-- The merged legs: laid end to end from 0, with distinct ids, each as good
-- as the leg of one of the copies it came from.
namespace Trip.Proofs

import Std (Float, Int, List, Nat, Option, Ord, DecEq, Eq, Void)
import Trip.Model (..)
import Trip.Merge (..)

-- Where legs end

-- With legs laid end to end from `at`, durations not negative, `at` is at
-- most the end of the trip.
theorem atLeLastEnd ∀ (s0: Float) (leg: Leg) (rest: List Leg)
    (h: ContiguousFrom s0 [leg, ..rest])
    (h1: List.All LegOk [leg, ..rest]):
    Float.leq s0 (lastEnd [leg, ..rest]) = True :=
  match rest, h, h1 with
    | [], Both e c, Both (Both pts (Both nonNeg fin)) oks => rewrite <- e in startLeEnd leg nonNeg
    | [next, ..more], Both e c, Both (Both pts (Both nonNeg fin)) oks =>
      floatLeTrans s0
        (s0 + leg.duration)
        (lastEnd [next, ..more])
        (Float.addMonotoneRight s0 leg.duration nonNeg)
        (atLeLastEnd (s0 + leg.duration) next more c oks)

-- Each leg starts no earlier than `at`, and ends no later than the trip.
theorem legBounds: ∀ (s0: Float) (legs: List Leg) => ContiguousFrom s0 legs
      → List.All LegOk legs
      → ∀ (leg: Leg) => leg ∈ legs → (Float.leq s0 leg.start = True) ∧ (Float.leq leg.end (lastEnd legs) = True)
  | s0, [], c, oks, leg, m => Void.exfalso m
  | s0, [first], Both e c, oks, leg, Inl same =>
    rewrite <- same in Both (rewrite e in floatLeRefl s0) (floatLeRefl first.end)
  | s0, [first], c, oks, leg, Inr m => Void.exfalso m
  | s0, [first, next, ..more], Both e c, Both (Both pts (Both nonNeg fin)) oks, leg, Inl same =>
    rewrite <- same in
      Both (rewrite e in floatLeRefl s0) (rewrite e in atLeLastEnd (s0 + first.duration) next more c oks)
  | s0, [first, next, ..more], Both e c, Both ok oks, leg, Inr m =>
    match legBounds (s0 + first.duration) [next, ..more] c oks leg m with
      | Both low high =>
        match ok with
          | Both pts (Both nonNeg fin) =>
            Both
              (floatLeTrans s0 (s0 + first.duration) leg.start (Float.addMonotoneRight s0 first.duration nonNeg) low)
              high

-- The end of the trip is not before 0.
theorem zeroLeLastEnd ∀ (legs: List Leg)
    (c: ContiguousFrom 0.0 legs)
    (oks: List.All LegOk legs):
    Float.leq 0.0 (lastEnd legs) = True :=
  match legs with
    | [] => floatLeRefl 0.0
    | [leg, ..rest] => atLeLastEnd 0.0 leg rest c oks

-- Laying legs out

theorem layoutContiguous ∀ (s0: Float) (legs: List Leg): ContiguousFrom s0 (layout s0 legs) := match legs with
  | [] => Trivial
  | [leg, ..rest] => Both rfl (layoutContiguous (s0 + leg.duration) rest)

theorem layoutIds ∀ (s0: Float) (legs: List Leg):
    List.map (layout s0 legs) (leg => leg.id) = List.map legs (leg => leg.id) :=
  match legs with
    | [] => rfl
    | [leg, ..rest] => Eq.cong (ids => [leg.id, ..ids]) (layoutIds (s0 + leg.duration) rest)

theorem shiftPointsIds ∀ (from to: Float) (points: List Point):
    List.map (shiftPoints from to points) (point => point.id) = List.map points (point => point.id) :=
  match c: from == to with
    | True => rfl
    | False => List.mapMap points (point => point.id) (point => { point | time = to + (point.time - from) })

theorem moveLegOk ∀ (s0: Float) (leg: Leg) (ok: LegOk leg): LegOk (moveLeg s0 leg) := match ok with
  | Both pts good => Both (rewrite shiftPointsIds leg.start s0 leg.points in pts) good

theorem layoutOk ∀ (s0: Float) (legs: List Leg) (h: List.All LegOk legs): List.All LegOk (layout s0 legs) :=
  match legs, h with
    | [], oks => Trivial
    | [leg, ..rest], Both ok oks => Both (moveLegOk s0 leg ok) (layoutOk (s0 + leg.duration) rest oks)

-- A leg laid where it already is stays as it is.
theorem moveLegSame ∀ (leg: Leg): moveLeg leg.start leg = leg := match leg with
  | { id, start, duration, points, notes = None } => rewrite DecEq.refl start in rfl
  | { id, start, duration, points, notes = Some notes } => rewrite DecEq.refl start in rfl

theorem layoutSame ∀ (s0: Float) (legs: List Leg) (h: ContiguousFrom s0 legs): layout s0 legs = legs :=
  match legs, h with
    | [], c => rfl
    | [leg, ..rest], Both e c =>
      calc layout s0 [leg, ..rest]
        _ = [moveLeg s0 leg, ..layout (s0 + leg.duration) rest]
        _ = [moveLeg leg.start leg, ..rest] := rewrite layoutSame (s0 + leg.duration) rest c, <- e in rfl
        _ = [leg, ..rest] := rewrite moveLegSame leg in rfl

-- Resolving a leg in both copies

theorem resolveAgainstId ∀ (local: List Leg) (remote: Leg): (resolveAgainst local remote).id = remote.id :=
  match c: findLeg local remote.id with
    | Some leg => rfl
    | None => rfl

theorem resolveOk ∀ (local remote: Leg) (a: LegOk local) (b: LegOk remote): LegOk (resolveLeg local remote) :=
  match c: Nat.leq (remote.points.length + 1) local.points.length with
    | True => a
    | False => b

theorem resolveAgainstOk ∀ (local: List Leg) (remote: Leg)
    (oks: List.All LegOk local)
    (ok: LegOk remote):
    LegOk (resolveAgainst local remote) :=
  match c: findLeg local remote.id with
    | Some leg =>
      resolveOk leg remote
        (List.memOfAll LegOk local oks leg (And.right (List.findSome local (l => l.id == remote.id) leg c)))
        ok
    | None => ok

-- The merged legs

def resolvedLegs (local remote: List Leg): List Leg := remote.map (leg => resolveAgainst local leg)

theorem resolvedIds ∀ (local remote: List Leg):
    List.map (resolvedLegs local remote) (leg => leg.id) = List.map remote (leg => leg.id) :=
  Eq.trans
    (List.mapMap remote (leg => leg.id) (leg => resolveAgainst local leg))
    (List.mapCong remote (leg => (resolveAgainst local leg).id) (leg => leg.id) (leg => resolveAgainstId local leg))

theorem mergeLegsContiguous ∀ (local remote: List Leg): ContiguousFrom 0.0 (mergeLegs local remote) :=
  layoutContiguous 0.0 (List.appendNewBy (resolvedLegs local remote) local (leg => leg.id))

theorem mergeLegsIds ∀ (local remote: List Leg)
    (dl: List.Distinct (List.map local (leg => leg.id)))
    (dr: List.Distinct (List.map remote (leg => leg.id))):
    List.Distinct (List.map (mergeLegs local remote) (leg => leg.id)) :=
  rewrite layoutIds 0.0 (List.appendNewBy (resolvedLegs local remote) local (leg => leg.id)) in
    List.distinctKeysAppendNewBy
      (resolvedLegs local remote)
      local
      (leg => leg.id)
      (rewrite resolvedIds local remote in dr)
      dl

theorem mergeLegsOk ∀ (local remote: List Leg)
    (okl: List.All LegOk local)
    (okr: List.All LegOk remote):
    List.All LegOk (mergeLegs local remote) :=
  layoutOk 0.0
    (List.appendNewBy (resolvedLegs local remote) local (leg => leg.id))
    (List.allOfMem LegOk (List.appendNewBy (resolvedLegs local remote) local (leg => leg.id)) (leg m =>
      match (List.memAppendNewBy leg (resolvedLegs local remote) local (l => l.id)).forward m with
        | Inl resolved =>
          List.anyElim
            (r => resolveAgainst local r = leg)
            (LegOk leg)
            remote
            (List.memMapAny remote (r => resolveAgainst local r) leg resolved)
            (r inRemote e => rewrite <- e in resolveAgainstOk local r okl (List.memOfAll LegOk remote okr r inRemote))
        | Inr (Both inLocal fresh) => List.memOfAll LegOk local okl leg inLocal))

-- Every remote leg's id is in the merge.
theorem remoteLegKept ∀ (local remote: List Leg) (leg: Leg)
    (m: leg ∈ remote):
    leg.id ∈ List.map (mergeLegs local remote) (l => l.id) :=
  rewrite layoutIds 0.0 (List.appendNewBy (resolvedLegs local remote) local (l => l.id)) in
    rewrite <- resolveAgainstId local leg in
      List.memMap
        (List.appendNewBy (resolvedLegs local remote) local (l => l.id))
        (resolveAgainst local leg)
        (List.memAppendLeft
          (resolveAgainst local leg)
          (resolvedLegs local remote)
          (List.differenceBy local (resolvedLegs local remote) (l => l.id))
          (List.memMap remote leg m (l => resolveAgainst local l)))
        (l => l.id)
