--| std's search gives the fastest times: from the start, what it settles
--| is reached in that time (`fromStartResult`) and no race there is faster
--| (`boundFrom`), so its time is the fastest (`fromStartFastest`), and a
--| fastest time is what it settles (`fastestFromStart`). The same search
--| from the end, every move taken back, gives the fastest times to the end
--| (`toEndFastest`, `fastestToEnd`).

namespace Aoc.Year2024.Day20.Proofs
import Aoc.Year2024.Day20 (..)
import Aoc.Common (Direction, Position, directions)
import Aoc.Year2024.Day20.Spec (..)
import Std (And, Bool, Eq, Exists, Graph, List, Map, Nat, Option, Void)

--| On track, and some moves from the start reach `position` in `time`.
def FromStart (racetrack: Racetrack) (position: Position) (time: Nat): Prop :=
  (onTrack racetrack position = True)
    ∧ (Exists (List Direction) (moves =>
      (race racetrack racetrack.start moves = Some position) ∧ (moves.length = time)))

--| On track, and some moves from `position` reach the end in `time`.
def ToEnd (racetrack: Racetrack) (position: Position) (time: Nat): Prop :=
  (onTrack racetrack position = True)
    ∧ (Exists (List Direction) (moves => (race racetrack position moves = Some racetrack.end) ∧ (moves.length = time)))

--| The only source is `source`.
theorem onlySource ∀ (source state: Position) (member: state ∈ [source]): state = source := match member with
  | Inl here => here.flipped
  | Inr none => none.impossible

--| The search from a start on track.
theorem fromStartResult ∀ (racetrack: Racetrack)
    (startOnTrack: onTrack racetrack racetrack.start = True):
    Graph.SearchResult racetrack.graph [(racetrack.start, 0)] (FromStart racetrack) racetrack.fromStart :=
  Graph.breadthFirstCorrect racetrack.graph
    [racetrack.start]
    (FromStart racetrack)
    (source member =>
      rewrite onlySource racetrack.start source member then
        Both startOnTrack (Witness [] (Both byComputing byComputing)))
    (state time reached next weight edge =>
      let (Both moves isOne) := edgesSound racetrack state next weight edge
      Exists.elim moves (direction moved =>
        Exists.elim reached.right (steps parts =>
          Both
            (edgeOnTrack racetrack state next weight edge)
            (Witness
              (steps ++ [direction])
              (Both
                (raceSnoc racetrack racetrack.start steps state parts.left direction next moved)
                (rewrite List.lengthAppend steps [direction], isOne, <- And.right parts then byComputing))))))
    (state next weight edge => And.right (edgesSound racetrack state next weight edge))

--| The search from an end on track, every move taken back.
theorem toEndResult ∀ (racetrack: Racetrack)
    (endOnTrack: onTrack racetrack racetrack.end = True):
    Graph.SearchResult racetrack.graph [(racetrack.end, 0)] (ToEnd racetrack) racetrack.toEnd :=
  Graph.breadthFirstCorrect racetrack.graph
    [racetrack.end]
    (ToEnd racetrack)
    (source member =>
      rewrite onlySource racetrack.end source member then Both endOnTrack (Witness [] (Both byComputing byComputing)))
    (state time reaches next weight edge =>
      let (Both moves isOne) := edgesSound racetrack state next weight edge
      Exists.elim moves (direction moved =>
        Exists.elim reaches.right (steps parts =>
          Both
            (edgeOnTrack racetrack state next weight edge)
            (Witness
              [opposite direction, ..steps]
              (Both
                (Eq.trans
                  (raceCons racetrack next
                    (opposite direction)
                    state
                    (moveBack racetrack state reaches.left direction next moved)
                    steps)
                  parts.left)
                (rewrite isOne, <- And.right parts then arithmetic))))))
    (state next weight edge => And.right (edgesSound racetrack state next weight edge))

--| Along any race, the search's bound grows by no more than its moves.
theorem boundFrom ∀ (racetrack: Racetrack) (result: Map Position Nat)
    (closed: ∀ (state: Position) (time: Nat) => result.get state = Some time
      → ∀ (next: Position) (weight: Nat) => (next, weight) ∈ racetrack.edges state
        → Graph.Bound result (time + weight) next):
    ∀ (position: Position) (time: Nat) => Graph.Bound result time position
      → ∀ (moves: List Direction) (last: Position) => race racetrack position moves = Some last
        → Graph.Bound result (time + moves.length) last
  | position, time, bound, [], last, ended =>
    rewrite <- Option.someInjective ended then
      Graph.boundWeaken result time (time + List.length ([]: List Direction)) position bound (arithmetic)
  | position, time, bound, [direction, ..rest], last, ended =>
    match moved: moveTo racetrack position direction with
      | Some next => Exists.elim bound (found both =>
        let stepped := closed position found both.left next 1 (edgesComplete racetrack position direction next moved)
        let along :=
          boundFrom racetrack result closed next
            (time + 1)
            (Graph.boundWeaken result (found + 1) (time + 1) next stepped (arithmetic [both.right]))
            rest
            last
            ended
        Graph.boundWeaken result
          (time + 1 + rest.length)
          (time + List.length [direction, ..rest])
          last
          along
          (arithmetic))

--| From track, a race to the end takes at least the search back's bound.
theorem boundTo ∀ (racetrack: Racetrack) (result: Map Position Nat)
    (endBound: Graph.Bound result 0 racetrack.end)
    (closed: ∀ (state: Position) (time: Nat) => result.get state = Some time
      → ∀ (next: Position) (weight: Nat) => (next, weight) ∈ racetrack.edges state
        → Graph.Bound result (time + weight) next):
    ∀ (position: Position) => onTrack racetrack position = True
      → ∀ (moves: List Direction) => race racetrack position moves = Some racetrack.end
        → Graph.Bound result moves.length position
  | position, onIt, [], ended => rewrite Option.someInjective ended then endBound
  | position, onIt, [direction, ..rest], ended =>
    match moved: moveTo racetrack position direction with
      | Some next =>
        let nextOnTrack := And.right (moveCases racetrack position direction next moved)
        Exists.elim (boundTo racetrack result endBound closed next nextOnTrack rest ended) (found both =>
          let stepped :=
            closed next found both.left position 1
              (edgesComplete racetrack next
                (opposite direction)
                position
                (moveBack racetrack position onIt direction next moved))
          Graph.boundWeaken result
            (found + 1)
            (List.length [direction, ..rest])
            position
            stepped
            (arithmetic [both.right]))

--| The search's time from the start is the fastest, to a position on track.
theorem fromStartFastest ∀ (racetrack: Racetrack)
    (startOnTrack: onTrack racetrack racetrack.start = True)
    (position: Position) (time: Nat)
    (found: racetrack.fromStart.get position = Some time):
    (IsFastest racetrack racetrack.start position time) ∧ (onTrack racetrack position = True) :=
  let (Both reachedAll (Both sourcesBound closed)) := fromStartResult racetrack startOnTrack
  let (Both onIt reached) := reachedAll position time found
  Both
    (Both reached (moves raced =>
      Exists.elim
        (boundFrom racetrack racetrack.fromStart closed racetrack.start 0
          (sourcesBound racetrack.start 0 (Inl byComputing))
          moves
          position
          raced)
        (other both =>
          let same: time = other := Option.someInjective (Eq.trans found.flipped both.left)
          arithmetic [same, both.right])))
    onIt

--| A fastest time from the start is the search's.
theorem fastestFromStart ∀ (racetrack: Racetrack)
    (startOnTrack: onTrack racetrack racetrack.start = True)
    (position: Position) (time: Nat)
    (fastest: IsFastest racetrack racetrack.start position time):
    racetrack.fromStart.get position = Some time :=
  let (Both reachedAll (Both sourcesBound closed)) := fromStartResult racetrack startOnTrack
  let (Both (Witness moves (Both raced length)) noFaster) := fastest
  Exists.elim
    (boundFrom racetrack racetrack.fromStart closed racetrack.start 0
      (sourcesBound racetrack.start 0 (Inl byComputing))
      moves
      position
      raced)
    (other both =>
      let (Both got le) := both
      Exists.elim (reachedAll position other got).right (otherMoves parts =>
        let atMost := noFaster otherMoves parts.left
        let same: time = other := arithmetic [le, atMost, length, parts.right]
        rewrite same then got))

--| The search's time to the end is the fastest, from a position on track.
theorem toEndFastest ∀ (racetrack: Racetrack)
    (endOnTrack: onTrack racetrack racetrack.end = True)
    (position: Position) (time: Nat)
    (found: racetrack.toEnd.get position = Some time):
    (IsFastest racetrack position racetrack.end time) ∧ (onTrack racetrack position = True) :=
  let (Both reachedAll (Both sourcesBound closed)) := toEndResult racetrack endOnTrack
  let (Both onIt reached) := reachedAll position time found
  Both
    (Both reached (moves raced =>
      Exists.elim
        (boundTo racetrack racetrack.toEnd
          (sourcesBound racetrack.end 0 (Inl byComputing))
          closed
          position
          onIt
          moves
          raced)
        (other both =>
          let same: time = other := Option.someInjective (Eq.trans found.flipped both.left)
          arithmetic [same, both.right])))
    onIt

--| A fastest time to the end, from track, is the search's.
theorem fastestToEnd ∀ (racetrack: Racetrack)
    (endOnTrack: onTrack racetrack racetrack.end = True) (position: Position)
    (onIt: onTrack racetrack position = True) (time: Nat)
    (fastest: IsFastest racetrack position racetrack.end time):
    racetrack.toEnd.get position = Some time :=
  let (Both reachedAll (Both sourcesBound closed)) := toEndResult racetrack endOnTrack
  let (Both (Witness moves (Both raced length)) noFaster) := fastest
  Exists.elim
    (boundTo racetrack racetrack.toEnd
      (sourcesBound racetrack.end 0 (Inl byComputing))
      closed
      position
      onIt
      moves
      raced)
    (other both =>
      let (Both got le) := both
      Exists.elim (reachedAll position other got).right (otherMoves parts =>
        let atMost := noFaster otherMoves parts.left
        let same: time = other := arithmetic [le, atMost, length, parts.right]
        rewrite same then got))
