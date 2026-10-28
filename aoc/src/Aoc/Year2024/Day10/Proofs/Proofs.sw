-- Day 10 proved: both parts compute the spec's sums, for every map
-- (`part1Correct`, `part2Correct`). The spec's trails are lists of ten
-- positions on the map; every hiking trail is one of them
-- (`trailsAreCandidates`), each once (`pathsDistinct`). The program's search
-- finds a trail's end once per trail (`countTrailEnds`) and only trail ends
-- (`memTrailEnds`). Its steps are the spec's (Steps.sw).

namespace Aoc.Year2024.Day10.Proofs
import Aoc.Year2024.Day10 (..)
import Aoc.Year2024.Day10.Spec (..)
import Std (And, Bool, DecEq, Eq, Iff, List, Nat, Option, Void)

-- The rest of a trail after `from`: each step one of the spec's, ending at a
-- 9.
def climbs (map: TopographicMap): (from: Position) → (rest: List Position) → Bool
  | from, Nil => map.heightAt from == Some 9
  | from, Cons next rest => isStep map from next && climbs map next rest

-- The spec's "ends at height 9" and "at each step", after the first
-- position, are `climbs`.
theorem endsAndSteps (map: TopographicMap): (from: Position) → (rest: List Position) →
    (((Cons from rest).last |> .flatMap map.heightAt) == Some 9 && (Cons from rest).zipWithNext.all (pair => isStep map pair.fst pair.snd))
      = climbs map from rest
  | from, Nil => Bool.andTrue _
  | from, Cons next rest =>
    match step: isStep map from next with
      | True => endsAndSteps map next rest
      | False => Bool.andFalse _

-- A hiking trail is a start at height 0 and a climb from it.
theorem trailCons (map: TopographicMap) (start: Position) (rest: List Position):
    isHikingTrail map (Cons start rest) = (map.heightAt start == Some 0 && climbs map start rest) :=
  rewrite <- endsAndSteps map start rest in rfl

theorem lengthFlatMap (f: a → List b): (xs: List a) → (xs.flatMap f).length = xs.sumBy (x => (f x).length)
  | Nil => rfl
  | Cons x rest =>
    rewrite List.sumByCons rest x (x => (f x).length), <- lengthFlatMap f rest in List.lengthAppend (f x) (rest.flatMap f)

theorem lengthFilter: (xs: List a) → (p: a → Bool) → (xs.filter p).length = xs.count p
  | Nil, p => rfl
  | Cons x rest, p =>
    rewrite List.countCons rest x p, <- lengthFilter rest p in
      match keep: p x with
        | True => rfl
        | False => rfl

theorem countFalse: (xs: List a) → xs.count (x => False) = 0
  | Nil => rfl
  | Cons x rest => countFalse rest

theorem countNone (xs: List a) (p: a → Bool) (none: (x: a) → x ∈ xs → p x = False): xs.count p = 0 :=
  rewrite List.countCongMem xs p (x => False) none in countFalse xs

theorem anyEmpty: (xs: List a) → (p: a → Bool) → xs.length = 0 → xs.any p = False
  | Nil, p, empty => rfl
  | Cons x rest, p, empty => Void.exfalso (omega)

-- Where a climb ends is a 9.
theorem endHeight (map: TopographicMap): (from: Position) → (rest: List Position) → (end: Position) → climbs map from rest = True →
    (Cons from rest).last = Some end → map.heightAt end = Some 9
  | from, Nil, end, climbing, last => rewrite <- Option.someInjective from end last in DecEq.sound _ _ climbing
  | from, Cons next rest, end, climbing, last => endHeight map next rest end (Bool.andRight _ _ climbing) last

-- The search finds exactly the ends of the climbs of `steps` steps.
theorem memTrailEnds (map: TopographicMap): (steps: Nat) → (from: Position) → (end: Position) →
    end ∈ map.trailEnds steps from ↔ (pathsOf map steps).any (rest => climbs map from rest && (Cons from rest).last == Some end) = True
  | Zero, from, end =>
    match nine: map.heightAt from == Some 9 with
      | True =>
        {
          forward = member =>
            match member with
              | Inl same => rewrite <- same, DecEq.refl (Some from) in rfl
              | Inr none => Void.exfalso none,
          backward = has =>
            match equal: Some from == Some end with
              | True => Inl (Option.someInjective from end (DecEq.sound _ _ equal))
              | False => Void.exfalso (Bool.falseNotTrue has)
        }
      | False => {
        forward = member => Void.exfalso member,
        backward = has => Void.exfalso (Bool.falseNotTrue has)
      }
  | Succ steps, from, end => {
    forward = member =>
      List.anyElim (next => end ∈ map.trailEnds steps next) _ (map.uphill from) (List.memFlatMapElim (map.trailEnds steps) end (map.uphill from) member)
        (next nextIn endIn =>
          let both := (memUphill map from next).forward nextIn
          List.anyTrueElim (pathsOf map steps) (rest => climbs map next rest && (Cons next rest).last == Some end) _
            ((memTrailEnds map steps next end).forward endIn)
            (rest restIn climbing =>
              List.anyOfMem (pathsOf map (Succ steps)) (path => climbs map from path && (Cons from path).last == Some end) (Cons next rest)
                (rewrite And.right both in climbing)
                (List.memFlatMapIntro (position => pathsOf map steps |> .map (Cons position)) next (Cons next rest) map.positions (And.left both)
                  (List.memMap (pathsOf map steps) rest restIn (Cons next))))),
    backward = has =>
      List.anyTrueElim (pathsOf map (Succ steps)) (path => climbs map from path && (Cons from path).last == Some end) _ has (path pathIn climbing =>
        List.anyElim (position => path ∈ (pathsOf map steps |> .map (Cons position))) _ map.positions
          (List.memFlatMapElim (position => pathsOf map steps |> .map (Cons position)) path map.positions pathIn)
          (next nextIn inMapped =>
            List.anyElim (rest => Cons next rest = path) _ (pathsOf map steps) (List.memMapAny (pathsOf map steps) (Cons next) path inMapped)
              (rest restIn built =>
                let found: ((isStep map from next && climbs map next rest) && (Cons next rest).last == Some end) = True := rewrite <- built at climbing
                let step := Bool.andLeft _ _ (Bool.andLeft _ _ found)
                let later := Bool.andIntro _ _ (Bool.andRight _ _ (Bool.andLeft _ _ found)) (Bool.andRight _ _ found)
                List.memFlatMapIntro (map.trailEnds steps) next end (map.uphill from) ((memUphill map from next).backward (Both nextIn step))
                  ((memTrailEnds map steps next end).backward
                    (List.anyOfMem (pathsOf map steps) (rest => climbs map next rest && (Cons next rest).last == Some end) rest later restIn)))))
  }

-- The search finds a climb's end once per climb.
theorem countTrailEnds (map: TopographicMap): (steps: Nat) → (from: Position) → (pathsOf map steps).count (climbs map from) = (map.trailEnds steps from).length
  | Zero, from =>
    match nine: map.heightAt from == Some 9 with
      | True => rfl
      | False => rfl
  | Succ steps, from =>
    rewrite List.countSumBy (pathsOf map (Succ steps)) (climbs map from),
      List.sumByFlatMap map.positions (path => Bool.toNat (climbs map from path)) (position => pathsOf map steps |> .map (Cons position)),
      lengthFlatMap (map.trailEnds steps) (map.uphill from),
      <- List.sumByPerm _ _ (uphillPerm map from) (next => (map.trailEnds steps next).length),
      List.sumByFilter map.positions (next => (map.trailEnds steps next).length) (isStep map from) in
      List.sumByCong map.positions (next => ((pathsOf map steps).map (Cons next)).sumBy (path => Bool.toNat (climbs map from path)))
        (next => if isStep map from next then (map.trailEnds steps next).length else 0) (next =>
        rewrite List.sumByMap (pathsOf map steps) (path => Bool.toNat (climbs map from path)) (Cons next) in
          match step: isStep map from next with
            | True => rewrite <- countTrailEnds map steps next in Eq.sym (List.countSumBy (pathsOf map steps) (climbs map next))
            | False => List.sumByZeroIntro (pathsOf map steps) _ (rest member => rfl))

-- From a 0, the spec's trails are the climbs.
theorem ratingAtZero (map: TopographicMap) (start: Position) (zero: map.heightAt start = Some 0):
    (trailsFrom map start).length = (pathsOf map 9).count (climbs map start) :=
  rewrite lengthFilter ((pathsOf map 9).map (Cons start)) (isHikingTrail map), List.countMap (pathsOf map 9) (isHikingTrail map) (Cons start) in
    List.countCongMem (pathsOf map 9) _ _ (rest member => rewrite trailCons map start rest, zero in rfl)

-- No trail starts anywhere but a 0.
theorem noTrailsOffZero (map: TopographicMap) (start: Position) (zero: (map.heightAt start == Some 0) = False): (trailsFrom map start).length = 0 :=
  rewrite lengthFilter ((pathsOf map 9).map (Cons start)) (isHikingTrail map), List.countMap (pathsOf map 9) (isHikingTrail map) (Cons start) in
    countNone (pathsOf map 9) _ (rest member => rewrite trailCons map start rest, zero in rfl)

theorem ratingCorrect (map: TopographicMap) (start: Position) (zero: map.heightAt start = Some 0): map.rating start = rating map start :=
  Eq.trans (Eq.sym (countTrailEnds map 9 start)) (Eq.sym (ratingAtZero map start zero))

-- From a 0, the 9s the search reaches are the ones the spec's trails reach.
theorem scoreCorrect (map: TopographicMap) (start: Position) (zero: map.heightAt start = Some 0): map.score start = score map start :=
  let ends := map.trailEnds 9 start
  let reached := (nine: Position) => map.heightAt nine == Some 9 && (trailsFrom map start).any (trail => trail.last == Some nine)
  rewrite <- lengthFilter map.positions reached in
    List.permLength ends.distinct (map.positions.filter reached)
      (List.permOfSameMembers ends.distinct (map.positions.filter reached) (List.distinctNoRepeats ends)
        (List.distinctFilter map.positions reached (positionsDistinct map))
        (nine member =>
          List.anyTrueElim (pathsOf map 9) (rest => climbs map start rest && (Cons start rest).last == Some nine) _
            ((memTrailEnds map 9 start nine).forward ((List.memDistinct nine ends).forward member))
            (rest restIn found =>
              let climbing := Bool.andLeft _ _ found
              let last := Bool.andRight _ _ found
              let height := endHeight map start rest nine climbing (DecEq.sound _ _ last)
              let hiking: isHikingTrail map (Cons start rest) = True := rewrite trailCons map start rest, zero in climbing
              let inTrails := List.memFilterIntro ((pathsOf map 9).map (Cons start)) (isHikingTrail map) (Cons start rest)
                (List.memMap (pathsOf map 9) rest restIn (Cons start)) hiking
              List.memFilterIntro map.positions reached nine (positionsComplete map nine 9 height)
                (Bool.andIntro _ _ (rewrite height in DecEq.refl (Some 9))
                  (List.anyOfMem (trailsFrom map start) (trail => trail.last == Some nine) (Cons start rest) last inTrails))))
        (nine member =>
          let both := List.memFilter map.positions reached nine member
          List.anyTrueElim (trailsFrom map start) (trail => trail.last == Some nine) _ (Bool.andRight _ _ (And.right both)) (trail trailIn last =>
            let candidate := List.memFilter ((pathsOf map 9).map (Cons start)) (isHikingTrail map) trail trailIn
            List.anyElim (rest => Cons start rest = trail) _ (pathsOf map 9) (List.memMapAny (pathsOf map 9) (Cons start) trail (And.left candidate))
              (rest restIn built =>
                let trailHiking := And.right candidate
                let hiking: isHikingTrail map (Cons start rest) = True := rewrite <- built at trailHiking
                let climbing := Bool.andRight _ _ (rewrite trailCons map start rest at hiking)
                let ending: ((Cons start rest).last == Some nine) = True := rewrite <- built at last
                (List.memDistinct nine ends).backward
                  ((memTrailEnds map 9 start nine).backward
                    (List.anyOfMem (pathsOf map 9) (rest => climbs map start rest && (Cons start rest).last == Some nine) rest
                      (Bool.andIntro _ _ climbing ending) restIn))))))

-- The spec's trailhead check.
def startsTrail (map: TopographicMap) (start: Position): Bool := (trailsFrom map start).length >= 1

-- One position's part of `sumOverTrailheads`.
theorem trailheadValue (map: TopographicMap) (programValue: Position → Nat) (specValue: Position → Nat)
    (agree: (start: Position) → map.heightAt start = Some 0 → programValue start = specValue start)
    (none: (start: Position) → (trailsFrom map start).length = 0 → specValue start = 0) (start: Position):
    (if map.heightAt start == Some 0 then programValue start else Add.zero) = (if startsTrail map start then specValue start else Add.zero) :=
  match zero: map.heightAt start == Some 0 with
    | True =>
      match some: startsTrail map start with
        | True => agree start (DecEq.sound _ _ zero)
        | False => Eq.trans (agree start (DecEq.sound _ _ zero)) (none start (omega))
    | False =>
      match some: startsTrail map start with
        | True => Void.exfalso (omega [noTrailsOffZero map start zero])
        | False => rfl

-- The program's trailheads, the 0s, give the spec's sum: a 0 that starts no
-- trail adds 0 either way.
theorem sumOverTrailheads (map: TopographicMap) (programValue: Position → Nat) (specValue: Position → Nat)
    (agree: (start: Position) → map.heightAt start = Some 0 → programValue start = specValue start)
    (none: (start: Position) → (trailsFrom map start).length = 0 → specValue start = 0):
    map.trailheads.sumBy programValue = (trailheads map).sumBy specValue :=
  Eq.trans (List.sumByFilter map.positions programValue (position => map.heightAt position == Some 0))
    (Eq.trans
      (List.sumByCong map.positions (start => if map.heightAt start == Some 0 then programValue start else Add.zero)
        (start => if startsTrail map start then specValue start else Add.zero) (trailheadValue map programValue specValue agree none))
      (Eq.sym (List.sumByFilter map.positions specValue (startsTrail map))))

theorem part1Correct (map: TopographicMap): solvePart1 map = part1 map :=
  sumOverTrailheads map map.score (score map) (scoreCorrect map) (start empty =>
    countNone map.positions _ (nine member => rewrite anyEmpty (trailsFrom map start) (trail => trail.last == Some nine) empty in Bool.andFalse _))

theorem part2Correct (map: TopographicMap): solvePart2 map = part2 map := sumOverTrailheads map map.rating (rating map) (ratingCorrect map) (start empty => empty)

-- A climb from height `height` has `9 - height` more positions, all on the
-- map.
theorem climbsPaths (map: TopographicMap): (from: Position) → (rest: List Position) → (height: Nat) → map.heightAt from = Some height →
    climbs map from rest = True → And (height + rest.length = 9) (rest ∈ pathsOf map rest.length)
  | from, Nil, height, known, climbing =>
    let nine := Option.someInjective height 9 (Eq.trans (Eq.sym known) (DecEq.sound _ _ climbing))
    Both (omega [nine]) (Inl rfl)
  | from, Cons next rest, height, known, climbing =>
    let higher := Bool.andRight _ _ (Bool.andLeft _ _ climbing)
    let nextHeight: map.heightAt next = Some (height + 1) := DecEq.sound _ _ (rewrite known at higher)
    let later := climbsPaths map next rest (height + 1) nextHeight (Bool.andRight _ _ climbing)
    Both (omega [And.left later])
      (List.memFlatMapIntro (position => pathsOf map rest.length |> .map (Cons position)) next (Cons next rest) map.positions
        (positionsComplete map next (height + 1) nextHeight) (List.memMap (pathsOf map rest.length) rest (And.right later) (Cons next)))

-- An empty path is no trail.
theorem emptyIsNoTrail (map: TopographicMap): isHikingTrail map Nil = False := rfl

-- Every hiking trail starts on the map and is one of `trailsFrom`'s: the
-- spec's ten positions miss none.
theorem trailsAreCandidates (map: TopographicMap) (start: Position) (rest: List Position) (hiking: isHikingTrail map (Cons start rest) = True):
    And (start ∈ map.positions) (Cons start rest ∈ trailsFrom map start) :=
  let both := rewrite trailCons map start rest at hiking
  let zero: map.heightAt start = Some 0 := DecEq.sound _ _ (Bool.andLeft _ _ both)
  let paths := climbsPaths map start rest 0 zero (Bool.andRight _ _ both)
  let ten: rest.length = 9 := omega [And.left paths]
  let restPath := And.right paths
  Both (positionsComplete map start 0 zero)
    (List.memFilterIntro ((pathsOf map 9).map (Cons start)) (isHikingTrail map) (Cons start rest)
      (List.memMap (pathsOf map 9) rest (rewrite ten at restPath) (Cons start)) hiking)

-- `pathsOf` lists each path once, so the spec counts distinct trails.
theorem pathsDistinct (map: TopographicMap): (count: Nat) → List.Distinct (pathsOf map count)
  | Zero => Both (none => none) Trivial
  | Succ count =>
    List.distinctFlatMap (position => pathsOf map count |> .map (Cons position)) (path => path.headOr { row = 0, column = 0 }) map.positions
      (positionsDistinct map)
      (position member => List.distinctMap (pathsOf map count) (pathsDistinct map count) (Cons position) (first second same => Eq.cong List.tailOf same))
      (position member path inMapped =>
        List.anyElim (rest => Cons position rest = path) _ (pathsOf map count) (List.memMapAny (pathsOf map count) (Cons position) path inMapped)
          (rest restIn built => rewrite <- built in rfl))
