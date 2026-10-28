-- The count: the program adds up, over the track, how many cheats from each
-- position save enough. Those cheats, listed (`counted`), are as many as
-- the program counts (`lengthCounted`), each once (`distinctCounted`), and
-- are exactly the cheats saving at least the threshold (`countedSound`,
-- `countedComplete`). So `countCheatsCorrect`: the program's count is the
-- number of such cheats, for every racetrack whose S and E are track.

namespace Aoc.Year2024.Day20.Proofs
import Aoc.Year2024.Day20 (..)
import Aoc.Year2024.Day20.Spec (..)
import Std (And, Bool, Eq, Exists, Iff, List, Map, Nat, Option, Set, Void)

-- The cheats from `start` that the program counts.
def countedFrom (fromStart: Map Position Nat) (toEnd: Map Position Nat) (honest: Nat) (length: Nat) (threshold: Nat) (start: Position):
    List Cheat :=
  match fromStart.get start with
    | Some before => start.around length |> .filter (savesFrom toEnd honest threshold start before) |> .map (end => ({ start, end }: Cheat))
    | None => Nil

-- The cheats the program counts.
def counted (racetrack: Racetrack) (fromStart: Map Position Nat) (toEnd: Map Position Nat) (honest: Nat) (length: Nat) (threshold: Nat):
    List Cheat :=
  racetrack.track.toList |> .flatMap (countedFrom fromStart toEnd honest length threshold)

-- From a start the search reached, the cheats counted.
theorem countedFromSome (fromStart: Map Position Nat) (toEnd: Map Position Nat) (honest: Nat) (length: Nat) (threshold: Nat) (start: Position)
    (before: Nat) (got: fromStart.get start = Some before):
    countedFrom fromStart toEnd honest length threshold start
      = (start.around length |> .filter (savesFrom toEnd honest threshold start before) |> .map (end => ({ start, end }: Cheat))) :=
  rewrite got in rfl

-- To an end the search back reached, whether the race is short enough.
theorem savesFromSome (toEnd: Map Position Nat) (honest: Nat) (threshold: Nat) (start: Position) (before: Nat) (end: Position) (after: Nat)
    (got: toEnd.get end = Some after):
    savesFrom toEnd honest threshold start before end = (before + start.distance end + after + threshold ≤ honest) :=
  rewrite got in rfl

-- As many cheats from `start` as the program counts there...
theorem lengthCountedFrom (fromStart: Map Position Nat) (toEnd: Map Position Nat) (honest: Nat) (length: Nat) (threshold: Nat)
    (start: Position):
    (countedFrom fromStart toEnd honest length threshold start).length = cheatsFrom fromStart toEnd honest length threshold start :=
  match got: fromStart.get start with
    | Some before =>
      let kept := start.around length |> .filter (savesFrom toEnd honest threshold start before)
      rewrite List.lengthMap kept (end => ({ start, end }: Cheat)) in
        List.lengthFilter (start.around length) (savesFrom toEnd honest threshold start before)
    | None => rfl

-- ...and so as many in all.
theorem lengthCounted (racetrack: Racetrack) (fromStart: Map Position Nat) (toEnd: Map Position Nat) (honest: Nat) (length: Nat)
    (threshold: Nat):
    (counted racetrack fromStart toEnd honest length threshold).length
      = (racetrack.track.toList |> .sumBy (cheatsFrom fromStart toEnd honest length threshold)) :=
  rewrite List.lengthFlatMap (countedFrom fromStart toEnd honest length threshold) racetrack.track.toList in
    List.sumByCong racetrack.track.toList _ _ (start => lengthCountedFrom fromStart toEnd honest length threshold start)

-- No cheat is counted twice.
theorem distinctCounted (racetrack: Racetrack) (fromStart: Map Position Nat) (toEnd: Map Position Nat) (honest: Nat) (length: Nat)
    (threshold: Nat): List.Distinct (counted racetrack fromStart toEnd honest length threshold) :=
  List.distinctFlatMap (countedFrom fromStart toEnd honest length threshold) (cheat => cheat.start) racetrack.track.toList
    (Map.keysDistinct racetrack.track.items)
    (start member =>
      match got: fromStart.get start with
        | Some before =>
          List.distinctMap (start.around length |> .filter (savesFrom toEnd honest threshold start before))
            (List.distinctFilter (start.around length) (savesFrom toEnd honest threshold start before) (distinctAround start length))
            (end => ({ start, end }: Cheat)) (first second same => Eq.cong (cheat => cheat.end) same)
        | None => Trivial)
    (start member cheat inStart =>
      match got: fromStart.get start with
        | Some before =>
          Exists.elim (List.memMapElim _ cheat _ inStart)
            (end both => rewrite <- And.right both in rfl)
        | None => Void.exfalso inStart)

-- A position listed by the track is on it, and the other way round.
theorem listedOnTrack (racetrack: Racetrack) (position: Position): Iff (position ∈ racetrack.track.toList) (onTrack racetrack position = True) :=
  Map.memKeys racetrack.track.items position

-- Every cheat counted saves at least the threshold.
theorem countedSound (racetrack: Racetrack) (startOnTrack: onTrack racetrack racetrack.start = True)
    (endOnTrack: onTrack racetrack racetrack.end = True) (length: Nat) (threshold: Nat) (honest: Nat)
    (honestFound: racetrack.fromStart.get racetrack.end = Some honest) (cheat: Cheat)
    (member: cheat ∈ counted racetrack racetrack.fromStart racetrack.toEnd honest length threshold):
    SavesAtLeast racetrack length threshold cheat :=
  let starts := racetrack.track.toList
  let fromStart := racetrack.fromStart
  let toEnd := racetrack.toEnd
  List.anyElim _ _ starts (List.memFlatMapElim (countedFrom fromStart toEnd honest length threshold) cheat starts member)
    (start startMember inStart =>
      match got: fromStart.get start with
        | None => Void.exfalso inStart
        | Some before =>
          let inList := inStart
          Exists.elim (List.memMapElim _ cheat _ inList) (end both =>
            let (Both endMember made) := both
            let (Both aroundMember saves) := List.memFilter (start.around length) (savesFrom toEnd honest threshold start before) end endMember
            match gotAfter: toEnd.get end with
              | None =>
                Void.exfalso (Bool.falseNotTrue saves)
              | Some after =>
                let fits: before + cheatTime ({ start, end }: Cheat) + after + threshold ≤ honest :=
                  saves
                let near: cheatTime ({ start, end }: Cheat) ≤ length := aroundSound start length end aroundMember
                let (Both afterFast endOn) := toEndFastest racetrack endOnTrack end after gotAfter
                rewrite <- made in
                  Both (Both ((listedOnTrack racetrack start).forward startMember) (Both endOn near))
                    (Witness honest
                      (Witness before
                        (Witness after
                          (Both (And.left (fromStartFastest racetrack startOnTrack racetrack.end honest honestFound))
                            (Both (And.left (fromStartFastest racetrack startOnTrack start before got)) (Both afterFast fits))))))))

-- Every cheat saving at least the threshold is counted.
theorem countedComplete (racetrack: Racetrack) (startOnTrack: onTrack racetrack racetrack.start = True)
    (endOnTrack: onTrack racetrack racetrack.end = True) (length: Nat) (threshold: Nat) (honest: Nat)
    (honestFound: racetrack.fromStart.get racetrack.end = Some honest):
    (cheat: Cheat) → SavesAtLeast racetrack length threshold cheat → cheat ∈ counted racetrack racetrack.fromStart racetrack.toEnd honest length threshold
  | { start, end }, saves =>
    let fromStart := racetrack.fromStart
    let toEnd := racetrack.toEnd
    let (Both (Both startOn (Both endOn near)) times) := saves
    Exists.elim times (fastest rest =>
      Exists.elim rest (before more =>
        Exists.elim more (after parts =>
          let (Both honestFast (Both beforeFast (Both afterFast fits))) := parts
          let sameHonest: honest = fastest :=
            Option.someInjective _ _ (Eq.trans (Eq.sym honestFound) (fastestFromStart racetrack startOnTrack racetrack.end fastest honestFast))
          let gotBefore := fastestFromStart racetrack startOnTrack start before beforeFast
          let gotAfter := fastestToEnd racetrack endOnTrack end endOn after afterFast
          let saved: savesFrom toEnd honest threshold start before end = True :=
            rewrite savesFromSome toEnd honest threshold start before end after gotAfter, sameHonest in fits
          List.memFlatMapIntro (countedFrom fromStart toEnd honest length threshold) start ({ start, end }: Cheat) racetrack.track.toList
            ((listedOnTrack racetrack start).backward startOn)
            (rewrite countedFromSome fromStart toEnd honest length threshold start before gotBefore in
              List.memMap (start.around length |> .filter (savesFrom toEnd honest threshold start before)) end
                (List.memFilterIntro (start.around length) (savesFrom toEnd honest threshold start before) end
                  (aroundComplete start length end near) saved)
                (other => ({ start, end = other }: Cheat))))))

-- The program's count is the number of cheats of up to `length`
-- picoseconds saving at least `threshold`.
theorem countCheatsCorrect (racetrack: Racetrack) (startOnTrack: onTrack racetrack racetrack.start = True)
    (endOnTrack: onTrack racetrack racetrack.end = True) (length: Nat) (threshold: Nat):
    IsCount racetrack length threshold (countCheats length threshold racetrack) :=
  match honestFound: racetrack.fromStart.get racetrack.end with
    | Some honest =>
      Witness (counted racetrack racetrack.fromStart racetrack.toEnd honest length threshold)
        (Both (distinctCounted racetrack racetrack.fromStart racetrack.toEnd honest length threshold)
          (Both
            (cheat => {
              forward = member => countedSound racetrack startOnTrack endOnTrack length threshold honest honestFound cheat member,
              backward = saves => countedComplete racetrack startOnTrack endOnTrack length threshold honest honestFound cheat saves
            })
            (lengthCounted racetrack racetrack.fromStart racetrack.toEnd honest length threshold)))
    | None =>
      Witness Nil
        (Both Trivial
          (Both
            (cheat => {
              forward = member => Void.exfalso member,
              backward = saves =>
                Exists.elim (And.right saves) (fastest rest =>
                  Exists.elim rest (before more =>
                    Exists.elim more (after parts =>
                      let found := fastestFromStart racetrack startOnTrack racetrack.end fastest (And.left parts)
                      Void.exfalso (Option.noneNotSome fastest (Eq.trans (Eq.sym honestFound) found)))))
            })
            rfl))

theorem part1Correct (racetrack: Racetrack) (startOnTrack: onTrack racetrack racetrack.start = True)
    (endOnTrack: onTrack racetrack racetrack.end = True) (threshold: Nat): IsCount racetrack 2 threshold (solvePart1 threshold racetrack) :=
  countCheatsCorrect racetrack startOnTrack endOnTrack 2 threshold

theorem part2Correct (racetrack: Racetrack) (startOnTrack: onTrack racetrack racetrack.start = True)
    (endOnTrack: onTrack racetrack racetrack.end = True) (threshold: Nat): IsCount racetrack 20 threshold (solvePart2 threshold racetrack) :=
  countCheatsCorrect racetrack startOnTrack endOnTrack 20 threshold
