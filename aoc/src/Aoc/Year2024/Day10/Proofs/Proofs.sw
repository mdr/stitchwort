--| Day 10 proved: both parts compute the spec's sums, for every map
--| (`part1Correct`, `part2Correct`). The spec's trails are lists of ten
--| positions on the map; every hiking trail is one of them
--| (`trailsAreCandidates`), each once (`pathsDistinct`). The program's search
--| finds a trail's end once per trail (`countTrailEnds`) and only trail ends
--| (`memTrailEnds`). Its steps are the spec's (Steps.sw).

namespace Aoc.Year2024.Day10.Proofs
import Aoc.Year2024.Day10 (..)
import Aoc.Year2024.Day10.Spec (..)
import Aoc.Common (Position)
import Std (And, Bool, DecEq, Eq, Iff, List, Nat, Option, Void)

--| The rest of a trail after `from`: each step one of the spec's, ending at a
--| 9.
def climbs (map: TopographicMap): (from: Position) → (rest: List Position) → Bool
  | from, [] => map.heightAt from == Some 9
  | from, [next, ..rest] => isStep map from next && climbs map next rest

--| The spec's "ends at height 9" and "at each step", after the first
--| position, are `climbs`.
theorem endsAndSteps (map: TopographicMap) (from: Position) (rest: List Position): (([from, ..rest].last |> .flatMap map.heightAt) == Some 9 && [from, ..rest].zipWithNext.all (pair => isStep map pair.fst pair.snd))
    = climbs map from rest :=
  match rest with
    | [] => Bool.andTrue _
    | [next, ..rest] =>
      match step: isStep map from next with
        | True => endsAndSteps map next rest
        | False => Bool.andFalse _

--| A hiking trail is a start at height 0 and a climb from it.
theorem trailCons (map: TopographicMap) (start: Position) (rest: List Position):
    isHikingTrail map [start, ..rest] = (map.heightAt start == Some 0 && climbs map start rest) :=
  rewrite <- endsAndSteps map start rest in rfl

--| Where a climb ends is a 9.
theorem endHeight (map: TopographicMap) (from: Position) (rest: List Position) (end: Position) (climbing: climbs map from rest = True)
    (last: [from, ..rest].last = Some end): map.heightAt end = Some 9 :=
  match rest with
    | [] => rewrite <- Option.someInjective last in climbing.read
    | [next, ..rest] =>
      let Both _ later := climbing
      endHeight map next rest end later last

--| The search finds exactly the ends of the climbs of `steps` steps.
theorem memTrailEnds (map: TopographicMap) (steps: Nat) (from end: Position):
    end ∈ map.trailEnds steps from ↔ (pathsOf map steps).any (rest => climbs map from rest && [from, ..rest].last == Some end) = True :=
  match steps with
    | Zero =>
      match nine: map.heightAt from == Some 9 with
        | True =>
          {
            forward = member =>
              match member with
                | Inl same => rewrite <- same, DecEq.refl (Some from) in rfl
                | Inr none => Void.exfalso none,
            backward = has =>
              match equal: Some from == Some end with
                | True => Inl (Option.someInjective (DecEq.sound equal))
          }
        | False => {
          forward = member => Void.exfalso member,
          backward = has => cases
        }
    | Succ steps => {
      forward = member =>
        List.anyElim (next => end ∈ map.trailEnds steps next) _ (map.uphill from) (List.memFlatMapElim (map.trailEnds steps) end (map.uphill from) member)
          (next nextIn endIn =>
            let both := (memUphill map from next).forward nextIn
            let Witness rest (Both restIn climbing) := (memTrailEnds map steps next end).forward endIn
            Witness [next, ..rest]
              (Both
                (List.memFlatMapIntro (position => pathsOf map steps |> .map (Cons position)) next [next, ..rest] map.positions (And.left both)
                  (List.memMap (pathsOf map steps) rest restIn (Cons next)))
                (rewrite And.right both in climbing))),
      backward = has =>
        let Witness path (Both pathIn climbing) := has
        List.anyElim (position => path ∈ (pathsOf map steps |> .map (Cons position))) _ map.positions
          (List.memFlatMapElim (position => pathsOf map steps |> .map (Cons position)) path map.positions pathIn)
          (next nextIn inMapped =>
            List.anyElim (rest => [next, ..rest] = path) _ (pathsOf map steps) (List.memMapAny (pathsOf map steps) (Cons next) path inMapped)
              (rest restIn built =>
                let found: ((isStep map from next && climbs map next rest) && [next, ..rest].last == Some end) = True := rewrite <- built at climbing
                let Both (Both step climbsRest) ending := found
                List.memFlatMapIntro (map.trailEnds steps) next end (map.uphill from) ((memUphill map from next).backward (Both nextIn step))
                  ((memTrailEnds map steps next end).backward (Witness rest (Both restIn (Both climbsRest ending))))))
    }

--| The search finds a climb's end once per climb.
theorem countTrailEnds (map: TopographicMap) (steps: Nat) (from: Position): (pathsOf map steps).count (climbs map from) = (map.trailEnds steps from).length :=
  match steps with
    | Zero =>
      match nine: map.heightAt from == Some 9 with
        | True => rfl
        | False => rfl
    | Succ steps =>
      rewrite List.countSumBy (pathsOf map (Succ steps)) (climbs map from),
        List.sumByFlatMap map.positions (path => Bool.toNat (climbs map from path)) (position => pathsOf map steps |> .map (Cons position)),
        List.lengthFlatMap (map.trailEnds steps) (map.uphill from),
        <- List.sumByPerm _ _ (uphillPerm map from) (next => (map.trailEnds steps next).length),
        List.sumByFilter map.positions (next => (map.trailEnds steps next).length) (isStep map from) in
        List.sumByCong map.positions (next => ((pathsOf map steps).map (Cons next)).sumBy (path => Bool.toNat (climbs map from path)))
          (next => if isStep map from next then (map.trailEnds steps next).length else 0) (next =>
          rewrite List.sumByMap (pathsOf map steps) (path => Bool.toNat (climbs map from path)) (Cons next) in
            match step: isStep map from next with
              | True => rewrite <- countTrailEnds map steps next in Eq.sym (List.countSumBy (pathsOf map steps) (climbs map next))
              | False => List.sumByZeroIntro (pathsOf map steps) _ (rest member => rfl))

--| From a 0, the spec's trails are the climbs.
theorem ratingAtZero (map: TopographicMap) (start: Position) (zero: map.heightAt start = Some 0):
    (trailsFrom map start).length = (pathsOf map 9).count (climbs map start) :=
  rewrite List.lengthFilter ((pathsOf map 9).map (Cons start)) (isHikingTrail map), List.countMap (pathsOf map 9) (isHikingTrail map) (Cons start) in
    List.countCongMem _ _ _ (rest member => rewrite trailCons map start rest, zero in rfl)

--| No trail starts anywhere but a 0.
theorem noTrailsOffZero (map: TopographicMap) (start: Position) (zero: (map.heightAt start == Some 0) = False): (trailsFrom map start).length = 0 :=
  rewrite List.lengthFilter ((pathsOf map 9).map (Cons start)) (isHikingTrail map), List.countMap (pathsOf map 9) (isHikingTrail map) (Cons start) in
    List.countNone (pathsOf map 9) _ (rest member => rewrite trailCons map start rest, zero in rfl)

theorem ratingCorrect (map: TopographicMap) (start: Position) (zero: map.heightAt start = Some 0): map.rating start = rating map start :=
  Eq.trans (Eq.sym (countTrailEnds map 9 start)) (Eq.sym (ratingAtZero map start zero))

--| From a 0, the 9s the search reaches are the ones the spec's trails reach.
theorem scoreCorrect (map: TopographicMap) (start: Position) (zero: map.heightAt start = Some 0): map.score start = score map start :=
  let ends := map.trailEnds 9 start
  let reached := (nine: Position) => map.heightAt nine == Some 9 && (trailsFrom map start).any (trail => trail.last == Some nine)
  rewrite <- List.lengthFilter map.positions reached in
    List.permLength ends.unique (map.positions.filter reached)
      (List.permOfSameMembers ends.unique (map.positions.filter reached) (List.distinctUnique ends)
        (List.distinctFilter map.positions reached (positionsDistinct map))
        (nine member =>
          let Witness rest (Both restIn found) := (memTrailEnds map 9 start nine).forward ((List.memUnique nine ends).forward member)
          let climbing := Bool.andLeft found
          let last := Bool.andRight found
          let height := endHeight map start rest nine climbing (DecEq.sound last)
          let hiking: isHikingTrail map [start, ..rest] = True := rewrite trailCons map start rest, zero in climbing
          let inTrails := List.memFilterIntro ((pathsOf map 9).map (Cons start)) (isHikingTrail map)
            (List.memMap (pathsOf map 9) rest restIn (Cons start)) hiking
          List.memFilterIntro map.positions reached (positionsComplete map nine 9 height)
            (Both (rewrite height in DecEq.refl (Some 9)) (Witness [start, ..rest] (Both inTrails last))))
        (nine member =>
          let both := List.memFilter map.positions reached member
          List.anyTrueElim (trailsFrom map start) (trail => trail.last == Some nine) _ (Bool.andRight (And.right both)) (trail trailIn last =>
            let candidate := List.memFilter ((pathsOf map 9).map (Cons start)) (isHikingTrail map) trailIn
            List.anyElim (rest => [start, ..rest] = trail) _ (pathsOf map 9) (List.memMapAny (pathsOf map 9) (Cons start) trail (And.left candidate))
              (rest restIn built =>
                let trailHiking := And.right candidate
                let hiking: isHikingTrail map [start, ..rest] = True := rewrite <- built at trailHiking
                let climbing := Bool.andRight (rewrite trailCons map start rest at hiking)
                let ending: ([start, ..rest].last == Some nine) = True := rewrite <- built at last
                (List.memUnique nine ends).backward
                  ((memTrailEnds map 9 start nine).backward (Witness rest (Both restIn (Bool.andIntro climbing ending))))))))

--| The spec's trailhead check.
def startsTrail (map: TopographicMap) (start: Position): Bool := (trailsFrom map start).length >= 1

--| One position's part of `sumOverTrailheads`.
theorem trailheadValue (map: TopographicMap) (programValue: Position → Nat) (specValue: Position → Nat)
    (agree: ∀ (start: Position) => map.heightAt start = Some 0 → programValue start = specValue start)
    (none: ∀ (start: Position) => (trailsFrom map start).length = 0 → specValue start = 0) (start: Position):
    (if map.heightAt start == Some 0 then programValue start else Add.zero) = (if startsTrail map start then specValue start else Add.zero) :=
  match zero: map.heightAt start == Some 0 with
    | True =>
      match some: startsTrail map start with
        | True => agree start zero.read
        | False => Eq.trans (agree start zero.read) (none start (omega))
    | False =>
      match some: startsTrail map start with
        | True => Void.exfalso (omega [noTrailsOffZero map start zero])
        | False => rfl

--| The program's trailheads, the 0s, give the spec's sum: a 0 that starts no
--| trail adds 0 either way.
theorem sumOverTrailheads (map: TopographicMap) (programValue: Position → Nat) (specValue: Position → Nat)
    (agree: ∀ (start: Position) => map.heightAt start = Some 0 → programValue start = specValue start)
    (none: ∀ (start: Position) => (trailsFrom map start).length = 0 → specValue start = 0):
    map.trailheads.sumBy programValue = (trailheads map).sumBy specValue :=
  Eq.trans (List.sumByFilter map.positions programValue (position => map.heightAt position == Some 0))
    (Eq.trans
      (List.sumByCong map.positions (start => if map.heightAt start == Some 0 then programValue start else Add.zero)
        (start => if startsTrail map start then specValue start else Add.zero) (trailheadValue map programValue specValue agree none))
      (Eq.sym (List.sumByFilter map.positions specValue (startsTrail map))))

theorem part1Correct (map: TopographicMap): solvePart1 map = part1 map :=
  sumOverTrailheads map map.score (score map) (scoreCorrect map) (start empty =>
    List.countNone map.positions _ (nine member => rewrite List.anyEmpty (trailsFrom map start) (trail => trail.last == Some nine) empty in Bool.andFalse _))

theorem part2Correct (map: TopographicMap): solvePart2 map = part2 map := sumOverTrailheads map map.rating (rating map) (ratingCorrect map) (start empty => empty)

--| A climb from height `height` has `9 - height` more positions, all on the
--| map.
theorem climbsPaths (map: TopographicMap) (from: Position) (rest: List Position) (height: Nat) (known: map.heightAt from = Some height)
    (climbing: climbs map from rest = True): (height + rest.length = 9) ∧ (rest ∈ pathsOf map rest.length) :=
  match rest with
    | [] =>
      let nine := Option.someInjective (Eq.trans (Eq.sym known) climbing.read)
      Both (omega [nine]) (Inl rfl)
    | [next, ..rest] =>
      let Both (Both _ higher) restClimbs := climbing
      let nextHeight: map.heightAt next = Some (height + 1) := DecEq.sound (rewrite known at higher)
      let later := climbsPaths map next rest (height + 1) nextHeight restClimbs
      Both (omega [And.left later])
        (List.memFlatMapIntro (position => pathsOf map rest.length |> .map (Cons position)) next [next, ..rest] map.positions
          (positionsComplete map next (height + 1) nextHeight) (List.memMap (pathsOf map rest.length) rest (And.right later) (Cons next)))

--| An empty path is no trail.
theorem emptyIsNoTrail (map: TopographicMap): isHikingTrail map [] = False := rfl

--| Every hiking trail starts on the map and is one of `trailsFrom`'s: the
--| spec's ten positions miss none.
theorem trailsAreCandidates (map: TopographicMap) (start: Position) (rest: List Position) (hiking: isHikingTrail map [start, ..rest] = True):
    (start ∈ map.positions) ∧ ([start, ..rest] ∈ trailsFrom map start) :=
  let both := rewrite trailCons map start rest at hiking
  let Both startsAtZero climbing := both
  let zero: map.heightAt start = Some 0 := DecEq.sound startsAtZero
  let paths := climbsPaths map start rest 0 zero climbing
  let ten: rest.length = 9 := omega [And.left paths]
  let restPath := And.right paths
  Both (positionsComplete map start 0 zero)
    (List.memFilterIntro ((pathsOf map 9).map (Cons start)) (isHikingTrail map)
      (List.memMap (pathsOf map 9) rest (rewrite ten at restPath) (Cons start)) hiking)

--| `pathsOf` lists each path once, so the spec counts distinct trails.
theorem pathsDistinct (map: TopographicMap) (count: Nat): List.Distinct (pathsOf map count) :=
  match count with
    | Zero => Both (none => none) Trivial
    | Succ count =>
      List.distinctFlatMap (position => pathsOf map count |> .map (Cons position)) (path => path.headOr { row = 0, column = 0 }) map.positions
        (positionsDistinct map)
        (position member => List.distinctMap (pathsOf map count) (pathsDistinct map count) (Cons position) (first second same => Eq.cong List.tailOf same))
        (position member path inMapped =>
          List.anyElim (rest => [position, ..rest] = path) _ (pathsOf map count) (List.memMapAny (pathsOf map count) (Cons position) path inMapped)
            (rest restIn built => rewrite <- built in rfl))
