-- Part 1: std's breadth-first search from the start settles each position
-- for the length of some walk there (`fromStartCorrect`). Each walk is a
-- walk in the graph as long (`stepsWalk`), so by std's `Graph.boundAlong` no
-- walk is shorter (`boundAlong`), the steps it finds to the exit are the
-- fewest of any path (`part1Some`), and finding none means there is no
-- path (`part1None`). Whether the exit is reachable is then whether there
-- is a path (`reachableSound`, `reachableComplete`).

namespace Aoc.Year2024.Day18.Proofs
import Aoc.Year2024.Day18 (..)
import Aoc.Year2024.Day18.Spec (..)
import Std (And, Bool, Eq, Exists, Graph, List, Map, Nat, Option, Void)

-- Some walk from the start ends at `position`, taking `cost` steps.
def ReachedFromStart (size: Nat) (fallen: List Position) (position: Position) (cost: Nat): Prop :=
  Exists (List Direction) (steps => And (walk size fallen Position.start steps = Some position) (steps.length = cost))

-- From a safe start, the search.
theorem fromStartSafe (memory: MemorySpace) (safe: memory.isSafe Position.start = True): memory.fromStart = memory.graph.breadthFirst [Position.start] :=
  rewrite safe in rfl

-- The search from a start.
theorem fromStartCorrect (size: Nat) (bytes: List Position) (fallen: Nat):
    Graph.SearchResult (MemorySpace.after size bytes fallen).graph ([Position.start].map (source => (source, 0))) (ReachedFromStart size (bytes.take fallen))
      ((MemorySpace.after size bytes fallen).graph.breadthFirst [Position.start]) :=
  let memory := MemorySpace.after size bytes fallen
  Graph.breadthFirstCorrect memory.graph [Position.start] (ReachedFromStart size (bytes.take fallen))
    (source member =>
      match member with
        | Inl here => rewrite <- here in Witness Nil (Both rfl rfl)
        | Inr none => Void.exfalso none)
    (state cost reached next weight edge =>
      let (Both moves costs) := memory.edgesSound state next weight edge
      Exists.elim moves (direction moved =>
        Exists.elim reached (steps parts =>
          Witness (steps ++ [direction])
            (Both
              (walkSnoc size (bytes.take fallen) Position.start steps state (And.left parts) direction next
                (Eq.trans (Eq.sym (moveAgrees size bytes fallen state direction)) moved))
              (rewrite List.lengthAppend steps [direction], costs, <- And.right parts in rfl)))))
    (state next weight edge => And.right (memory.edgesSound state next weight edge))

-- A walk is a walk in the graph, as long.
theorem stepsWalk (size: Nat) (bytes: List Position) (fallen: Nat): (position: Position) → (steps: List Direction) → (last: Position) →
    walk size (bytes.take fallen) position steps = Some last →
    Exists (List (Position, Nat)) (path => And ((MemorySpace.after size bytes fallen).graph.Walk position path last) (Graph.cost path = steps.length))
  | position, Nil, last, ended => Witness Nil (Both (Option.someInjective _ _ ended) rfl)
  | position, Cons direction rest, last, ended =>
    match moved: stepTo size (bytes.take fallen) position direction with
      | None => Void.exfalso (Option.noneNotSome last ended)
      | Some next =>
        Exists.elim (stepsWalk size bytes fallen next rest last ended) (path both =>
          Witness (Cons (next, 1) path)
            (Both
              (Both
                (edgesComplete (MemorySpace.after size bytes fallen) position direction next
                  (Eq.trans (moveAgrees size bytes fallen position direction) moved))
                (And.left both))
              (omega [Graph.costCons next 1 path, And.right both])))

-- Along any walk, the search's bound grows by no more than its steps.
theorem boundAlong (size: Nat) (bytes: List Position) (fallen: Nat) (result: Map Position Nat)
    (closed: (state: Position) → (cost: Nat) → result.get state = Some cost → (next: Position) → (weight: Nat) →
      (next, weight) ∈ (MemorySpace.after size bytes fallen).graph.edges state → Graph.Bound result (cost + weight) next)
    (position: Position) (cost: Nat) (bound: Graph.Bound result cost position) (steps: List Direction) (last: Position)
    (ended: walk size (bytes.take fallen) position steps = Some last): Graph.Bound result (cost + steps.length) last :=
  Exists.elim (stepsWalk size bytes fallen position steps last ended) (path both =>
    rewrite <- And.right both in Graph.boundAlong (MemorySpace.after size bytes fallen).graph result closed position cost bound path last (And.left both))

-- When part 1 finds a number of steps, it is the fewest of any path.
theorem part1Some (size: Nat) (bytes: List Position) (fallen: Nat) (fewest: Nat) (answer: solvePart1 size fallen bytes = Some fewest):
    IsFewestSteps size (bytes.take fallen) fewest :=
  let memory := MemorySpace.after size bytes fallen
  let found: memory.fromStart.get memory.exit = Some fewest := answer
  match startSafe: memory.isSafe Position.start with
    | False => Void.exfalso (Option.noneNotSome fewest found)
    | True =>
      let (Both reachedAll (Both sourcesBound closed)) := fromStartCorrect size bytes fallen
      let startSpec: isSafe size (bytes.take fallen) Position.start = True := Eq.trans (Eq.sym (safeAgrees size bytes fallen Position.start)) startSafe
      Both
        (Exists.elim (reachedAll _ fewest found) (steps parts => Witness steps (Both (Both startSpec (And.left parts)) (And.right parts))))
        (steps path =>
          Exists.elim
            (boundAlong size bytes fallen _ closed Position.start 0 (sourcesBound Position.start 0 (Inl rfl)) steps memory.exit (And.right path))
            (other both =>
              let same: fewest = other := Option.someInjective _ _ (Eq.trans (Eq.sym found) (And.left both))
              omega [same, And.right both]))

-- When part 1 finds no number of steps, there is no path.
theorem part1None (size: Nat) (bytes: List Position) (fallen: Nat) (answer: solvePart1 size fallen bytes = None) (steps: List Direction)
    (path: IsPath size (bytes.take fallen) steps): Void :=
  let memory := MemorySpace.after size bytes fallen
  let startSafe: memory.isSafe Position.start = True := Eq.trans (safeAgrees size bytes fallen Position.start) (And.left path)
  let missing: (memory.graph.breadthFirst [Position.start]).get memory.exit = None :=
    Eq.trans (Eq.cong (settled => settled.get memory.exit) (Eq.sym (fromStartSafe memory startSafe))) answer
  let (Both reachedAll (Both sourcesBound closed)) := fromStartCorrect size bytes fallen
  Exists.elim (boundAlong size bytes fallen _ closed Position.start 0 (sourcesBound Position.start 0 (Inl rfl)) steps memory.exit (And.right path))
    (other both => Option.noneNotSome other (Eq.trans (Eq.sym missing) (And.left both)))

-- Reachable means there is a path...
theorem reachableSound (size: Nat) (bytes: List Position) (fallen: Nat) (open: reachable size bytes fallen = True): HasPath size bytes fallen :=
  let some: (solvePart1 size fallen bytes).isSome = True := open
  match answer: solvePart1 size fallen bytes with
    | Some fewest => Exists.elim (And.left (part1Some size bytes fallen fewest answer)) (steps both => Witness steps (And.left both))
    | None => Void.exfalso (Bool.falseNotTrue some)

-- ...and a path means reachable.
theorem reachableComplete (size: Nat) (bytes: List Position) (fallen: Nat) (has: HasPath size bytes fallen): reachable size bytes fallen = True :=
  let some: (solvePart1 size fallen bytes).isSome = True :=
    match answer: solvePart1 size fallen bytes with
      | Some fewest => rfl
      | None => Exists.elim has (steps path => Void.exfalso (part1None size bytes fallen answer steps path))
  some
