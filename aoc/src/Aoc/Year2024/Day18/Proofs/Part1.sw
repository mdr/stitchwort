-- Part 1: day 16's search from the start settles each position for the
-- length of some walk there (`fromStartCorrect`), and no walk is shorter
-- (`boundAlong`), so the steps it finds to the exit are the fewest of any
-- path (`part1Some`), and finding none means there is no path
-- (`part1None`). Whether the exit is reachable is then whether there is a
-- path (`reachableSound`, `reachableComplete`).

namespace Aoc.Year2024.Day18.Proofs
import Aoc.Year2024.Day18 (..)
import Aoc.Year2024.Day18.Spec (..)
import Aoc.Year2024.Day16.Proofs (Bound, SearchResult, boundWeaken, distancesCorrect)
import Std (And, Bool, Eq, Exists, List, Map, Nat, Option, Void)

-- Some walk from the start ends at `position`, taking `cost` steps.
def ReachedFromStart (size: Nat) (fallen: List Position) (position: Position) (cost: Nat): Prop :=
  Exists (List Direction) (steps => And (walk size fallen start steps = Some position) (steps.length = cost))

-- From a safe start, the search.
theorem fromStartSafe (memory: MemorySpace) (safe: memory.isSafe start = True): memory.fromStart = memory.graph.distances [(start, 0)] :=
  rewrite safe in rfl

-- The search from a safe start.
theorem fromStartCorrect (size: Nat) (bytes: List Position) (fallen: Nat) (startSafe: (MemorySpace.after size bytes fallen).isSafe start = True):
    SearchResult (MemorySpace.after size bytes fallen).graph [(start, 0)] (ReachedFromStart size (bytes.take fallen))
      ((MemorySpace.after size bytes fallen).graph.distances [(start, 0)]) :=
  let memory := MemorySpace.after size bytes fallen
  distancesCorrect memory.graph [(start, 0)] (ReachedFromStart size (bytes.take fallen))
    (source cost member =>
      match member with
        | Inl here => rewrite <- Eq.cong Pair.fst here, <- Eq.cong Pair.snd here in Witness Nil (Both rfl rfl)
        | Inr none => Void.exfalso none)
    (source cost member =>
      match member with
        | Inl here => rewrite <- Eq.cong Pair.fst here in startSafe
        | Inr none => Void.exfalso none)
    (state cost reached next weight edge =>
      let (Both moves costs) := edgesSound memory state next weight edge
      Exists.elim moves (direction moved =>
        Exists.elim reached (steps parts =>
          Witness (steps ++ [direction])
            (Both
              (walkSnoc size (bytes.take fallen) start steps state (And.left parts) direction next
                (Eq.trans (Eq.sym (moveAgrees size bytes fallen state direction)) moved))
              (rewrite List.lengthAppend steps [direction], costs, <- And.right parts in rfl)))))
    (state safe next weight edge =>
      let (Both moves costs) := edgesSound memory state next weight edge
      Exists.elim moves (direction moved => moveSafe memory state direction next moved))

-- Along any walk, the search's bound grows by no more than its steps.
theorem boundAlong (size: Nat) (bytes: List Position) (fallen: Nat) (result: Map Position Nat)
    (closed: (state: Position) → (cost: Nat) → result.get state = Some cost → (next: Position) → (weight: Nat) →
      (next, weight) ∈ (MemorySpace.after size bytes fallen).edges state → Bound result (cost + weight) next):
    (position: Position) → (cost: Nat) → Bound result cost position → (steps: List Direction) → (last: Position) →
      walk size (bytes.take fallen) position steps = Some last → Bound result (cost + steps.length) last
  | position, cost, bound, Nil, last, ended =>
    rewrite <- Option.someInjective _ _ ended in boundWeaken result cost (cost + List.length (Nil: List Direction)) position bound (omega)
  | position, cost, bound, Cons direction rest, last, ended =>
    match moved: stepTo size (bytes.take fallen) position direction with
      | None => Void.exfalso (Option.noneNotSome last ended)
      | Some next =>
        Exists.elim bound (found both =>
          let edge := edgesComplete (MemorySpace.after size bytes fallen) position direction next
            (Eq.trans (moveAgrees size bytes fallen position direction) moved)
          let stepped := closed position found (And.left both) next 1 edge
          let along := boundAlong size bytes fallen result closed next (cost + 1)
            (boundWeaken result (found + 1) (cost + 1) next stepped (omega [And.right both])) rest last ended
          boundWeaken result (cost + 1 + rest.length) (cost + List.length (Cons direction rest)) last along (omega))

-- When part 1 finds a number of steps, it is the fewest of any path.
theorem part1Some (size: Nat) (bytes: List Position) (fallen: Nat) (fewest: Nat) (answer: solvePart1 size fallen bytes = Some fewest):
    IsFewestSteps size (bytes.take fallen) fewest :=
  let memory := MemorySpace.after size bytes fallen
  let found: memory.fromStart.get memory.exit = Some fewest := answer
  match startSafe: memory.isSafe start with
    | False => Void.exfalso (Option.noneNotSome fewest found)
    | True =>
      let (Both reachedAll (Both sourcesBound closed)) := fromStartCorrect size bytes fallen startSafe
      let startSpec: isSafe size (bytes.take fallen) start = True := Eq.trans (Eq.sym (safeAgrees size bytes fallen start)) startSafe
      Both
        (Exists.elim (reachedAll _ fewest found) (steps parts => Witness steps (Both (Both startSpec (And.left parts)) (And.right parts))))
        (steps path =>
          Exists.elim
            (boundAlong size bytes fallen _ closed start 0 (sourcesBound start 0 (Inl rfl)) steps memory.exit (And.right path))
            (other both =>
              let same: fewest = other := Option.someInjective _ _ (Eq.trans (Eq.sym found) (And.left both))
              omega [same, And.right both]))

-- When part 1 finds no number of steps, there is no path.
theorem part1None (size: Nat) (bytes: List Position) (fallen: Nat) (answer: solvePart1 size fallen bytes = None) (steps: List Direction)
    (path: IsPath size (bytes.take fallen) steps): Void :=
  let memory := MemorySpace.after size bytes fallen
  let startSafe: memory.isSafe start = True := Eq.trans (safeAgrees size bytes fallen start) (And.left path)
  let missing: (memory.graph.distances [(start, 0)]).get memory.exit = None :=
    Eq.trans (Eq.cong (settled => settled.get memory.exit) (Eq.sym (fromStartSafe memory startSafe))) answer
  let (Both reachedAll (Both sourcesBound closed)) := fromStartCorrect size bytes fallen startSafe
  Exists.elim (boundAlong size bytes fallen _ closed start 0 (sourcesBound start 0 (Inl rfl)) steps memory.exit (And.right path))
    (other both => Option.noneNotSome other (Eq.trans (Eq.sym missing) (And.left both)))

-- Reachable means there is a path...
theorem reachableSound (size: Nat) (bytes: List Position) (fallen: Nat) (open: reachable size bytes fallen = True): HasPath size bytes fallen
    unfolding reachable
:=
  let some: (solvePart1 size fallen bytes).isSome = True := open
  match answer: solvePart1 size fallen bytes with
    | Some fewest => Exists.elim (And.left (part1Some size bytes fallen fewest answer)) (steps both => Witness steps (And.left both))
    | None => Void.exfalso (Bool.falseNotTrue some)

-- ...and a path means reachable.
theorem reachableComplete (size: Nat) (bytes: List Position) (fallen: Nat) (has: HasPath size bytes fallen): reachable size bytes fallen = True
    unfolding reachable
:=
  let some: (solvePart1 size fallen bytes).isSome = True :=
    match answer: solvePart1 size fallen bytes with
      | Some fewest => rfl
      | None => Exists.elim has (steps path => Void.exfalso (part1None size bytes fallen answer steps path))
  some
