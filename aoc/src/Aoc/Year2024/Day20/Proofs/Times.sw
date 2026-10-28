-- Day 16's search gives the fastest times: from the start, what it settles
-- is reached in that time (`fromStartResult`) and no race there is faster
-- (`boundFrom`), so its time is the fastest (`fromStartFastest`), and a
-- fastest time is what it settles (`fastestFromStart`). The same search
-- from the end, every move taken back, gives the fastest times to the end
-- (`toEndFastest`, `fastestToEnd`).

namespace Aoc.Year2024.Day20.Proofs
import Aoc.Year2024.Day20 (..)
import Aoc.Year2024.Day20.Spec (..)
import Aoc.Year2024.Day16.Proofs (Bound, SearchResult, boundWeaken, distancesCorrect)
import Std (And, Bool, Eq, Exists, List, Map, Nat, Option, Void)

-- On track, and some moves from the start reach `position` in `time`.
def FromStart (racetrack: Racetrack) (position: Position) (time: Nat): Prop :=
  And (onTrack racetrack position = True)
    (Exists (List Direction) (moves => And (race racetrack racetrack.start moves = Some position) (moves.length = time)))

-- On track, and some moves from `position` reach the end in `time`.
def ToEnd (racetrack: Racetrack) (position: Position) (time: Nat): Prop :=
  And (onTrack racetrack position = True)
    (Exists (List Direction) (moves => And (race racetrack position moves = Some racetrack.end) (moves.length = time)))

-- The only source is `source`, at 0.
theorem onlySource (source: Position) (state: Position) (start: Nat) (member: (state, start) ∈ [(source, 0)]): And (state = source) (start = 0) :=
  match member with
    | Inl here => Both (Eq.sym (Eq.cong Pair.fst here)) (Eq.sym (Eq.cong Pair.snd here))
    | Inr none => Void.exfalso none

-- The search from a start on track.
theorem fromStartResult (racetrack: Racetrack) (startOnTrack: onTrack racetrack racetrack.start = True):
    SearchResult racetrack.graph [(racetrack.start, 0)] (FromStart racetrack) racetrack.fromStart :=
  distancesCorrect racetrack.graph [(racetrack.start, 0)] (FromStart racetrack)
    (source start member =>
      let (Both atStart isZero) := onlySource racetrack.start source start member
      rewrite atStart, isZero in Both startOnTrack (Witness Nil (Both rfl rfl)))
    (source start member => rewrite And.left (onlySource racetrack.start source start member) in startOnTrack)
    (state time reached next weight edge =>
      let (Both moves isOne) := edgesSound racetrack state next weight edge
      Exists.elim moves (direction moved =>
        Exists.elim (And.right reached) (steps parts =>
          Both (edgeOnTrack racetrack state next weight edge)
            (Witness (steps ++ [direction])
              (Both (raceSnoc racetrack racetrack.start steps state (And.left parts) direction next moved)
                (rewrite List.lengthAppend steps [direction], isOne, <- And.right parts in rfl))))))
    (state onIt next weight edge => edgeOnTrack racetrack state next weight edge)

-- The search from an end on track, every move taken back.
theorem toEndResult (racetrack: Racetrack) (endOnTrack: onTrack racetrack racetrack.end = True):
    SearchResult racetrack.graph [(racetrack.end, 0)] (ToEnd racetrack) racetrack.toEnd :=
  distancesCorrect racetrack.graph [(racetrack.end, 0)] (ToEnd racetrack)
    (source start member =>
      let (Both atEnd isZero) := onlySource racetrack.end source start member
      rewrite atEnd, isZero in Both endOnTrack (Witness Nil (Both rfl rfl)))
    (source start member => rewrite And.left (onlySource racetrack.end source start member) in endOnTrack)
    (state time reaches next weight edge =>
      let (Both moves isOne) := edgesSound racetrack state next weight edge
      Exists.elim moves (direction moved =>
        Exists.elim (And.right reaches) (steps parts =>
          Both (edgeOnTrack racetrack state next weight edge)
            (Witness (Cons (opposite direction) steps)
              (Both
                (Eq.trans (raceCons racetrack next (opposite direction) state (moveBack racetrack state (And.left reaches) direction next moved) steps)
                  (And.left parts))
                (rewrite isOne, <- And.right parts in omega))))))
    (state onIt next weight edge => edgeOnTrack racetrack state next weight edge)

-- Along any race, the search's bound grows by no more than its moves.
theorem boundFrom (racetrack: Racetrack) (result: Map Position Nat)
    (closed: (state: Position) → (time: Nat) → result.get state = Some time → (next: Position) → (weight: Nat) →
      (next, weight) ∈ racetrack.edges state → Bound result (time + weight) next):
    (position: Position) → (time: Nat) → Bound result time position → (moves: List Direction) → (last: Position) →
      race racetrack position moves = Some last → Bound result (time + moves.length) last
  | position, time, bound, Nil, last, ended =>
    rewrite <- Option.someInjective _ _ ended in boundWeaken result time (time + List.length (Nil: List Direction)) position bound (omega)
  | position, time, bound, Cons direction rest, last, ended =>
    match moved: moveTo racetrack position direction with
      | None => Void.exfalso (Option.noneNotSome last ended)
      | Some next =>
        Exists.elim bound (found both =>
          let stepped := closed position found (And.left both) next 1 (edgesComplete racetrack position direction next moved)
          let along := boundFrom racetrack result closed next (time + 1)
            (boundWeaken result (found + 1) (time + 1) next stepped (omega [And.right both])) rest last ended
          boundWeaken result (time + 1 + rest.length) (time + List.length (Cons direction rest)) last along (omega))

-- From track, a race to the end takes at least the search back's bound.
theorem boundTo (racetrack: Racetrack) (result: Map Position Nat) (endBound: Bound result 0 racetrack.end)
    (closed: (state: Position) → (time: Nat) → result.get state = Some time → (next: Position) → (weight: Nat) →
      (next, weight) ∈ racetrack.edges state → Bound result (time + weight) next):
    (position: Position) → onTrack racetrack position = True → (moves: List Direction) → race racetrack position moves = Some racetrack.end →
      Bound result moves.length position
  | position, onIt, Nil, ended => rewrite Option.someInjective _ _ ended in endBound
  | position, onIt, Cons direction rest, ended =>
    match moved: moveTo racetrack position direction with
      | None => Void.exfalso (Option.noneNotSome racetrack.end ended)
      | Some next =>
        let nextOnTrack := And.right (moveCases racetrack position direction next moved)
        Exists.elim (boundTo racetrack result endBound closed next nextOnTrack rest ended) (found both =>
          let stepped := closed next found (And.left both) position 1
            (edgesComplete racetrack next (opposite direction) position (moveBack racetrack position onIt direction next moved))
          boundWeaken result (found + 1) (List.length (Cons direction rest)) position stepped (omega [And.right both]))

-- The search's time from the start is the fastest, to a position on track.
theorem fromStartFastest (racetrack: Racetrack) (startOnTrack: onTrack racetrack racetrack.start = True) (position: Position) (time: Nat)
    (found: racetrack.fromStart.get position = Some time):
    And (IsFastest racetrack racetrack.start position time) (onTrack racetrack position = True) :=
  let (Both reachedAll (Both sourcesBound closed)) := fromStartResult racetrack startOnTrack
  let (Both onIt reached) := reachedAll position time found
  Both
    (Both reached
      (moves raced =>
        Exists.elim
          (boundFrom racetrack racetrack.fromStart closed racetrack.start 0 (sourcesBound racetrack.start 0 (Inl rfl)) moves position raced)
          (other both =>
            let same: time = other := Option.someInjective _ _ (Eq.trans (Eq.sym found) (And.left both))
            omega [same, And.right both])))
    onIt

-- A fastest time from the start is the search's.
theorem fastestFromStart (racetrack: Racetrack) (startOnTrack: onTrack racetrack racetrack.start = True) (position: Position) (time: Nat)
    (fastest: IsFastest racetrack racetrack.start position time): racetrack.fromStart.get position = Some time :=
  let (Both reachedAll (Both sourcesBound closed)) := fromStartResult racetrack startOnTrack
  let (Both (Witness moves (Both raced length)) noFaster) := fastest
  Exists.elim
    (boundFrom racetrack racetrack.fromStart closed racetrack.start 0 (sourcesBound racetrack.start 0 (Inl rfl)) moves position raced)
    (other both =>
      let (Both got le) := both
      Exists.elim (And.right (reachedAll position other got)) (otherMoves parts =>
        let atMost := noFaster otherMoves (And.left parts)
        let same: time = other := omega [le, atMost, length, And.right parts]
        rewrite same in got))

-- The search's time to the end is the fastest, from a position on track.
theorem toEndFastest (racetrack: Racetrack) (endOnTrack: onTrack racetrack racetrack.end = True) (position: Position) (time: Nat)
    (found: racetrack.toEnd.get position = Some time):
    And (IsFastest racetrack position racetrack.end time) (onTrack racetrack position = True) :=
  let (Both reachedAll (Both sourcesBound closed)) := toEndResult racetrack endOnTrack
  let (Both onIt reached) := reachedAll position time found
  Both
    (Both reached
      (moves raced =>
        Exists.elim (boundTo racetrack racetrack.toEnd (sourcesBound racetrack.end 0 (Inl rfl)) closed position onIt moves raced)
          (other both =>
            let same: time = other := Option.someInjective _ _ (Eq.trans (Eq.sym found) (And.left both))
            omega [same, And.right both])))
    onIt

-- A fastest time to the end, from track, is the search's.
theorem fastestToEnd (racetrack: Racetrack) (endOnTrack: onTrack racetrack racetrack.end = True) (position: Position)
    (onIt: onTrack racetrack position = True) (time: Nat) (fastest: IsFastest racetrack position racetrack.end time):
    racetrack.toEnd.get position = Some time :=
  let (Both reachedAll (Both sourcesBound closed)) := toEndResult racetrack endOnTrack
  let (Both (Witness moves (Both raced length)) noFaster) := fastest
  Exists.elim (boundTo racetrack racetrack.toEnd (sourcesBound racetrack.end 0 (Inl rfl)) closed position onIt moves raced)
    (other both =>
      let (Both got le) := both
      Exists.elim (And.right (reachedAll position other got)) (otherMoves parts =>
        let atMost := noFaster otherMoves (And.left parts)
        let same: time = other := omega [le, atMost, length, And.right parts]
        rewrite same in got))
