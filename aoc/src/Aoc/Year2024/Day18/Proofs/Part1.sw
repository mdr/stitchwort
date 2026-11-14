--| Part 1: std's breadth-first search from the start
--| (`Graph.breadthFirstShortest`) settles each position for the cost of
--| some walk there, and no walk there costs less. A walk is a path of the
--| spec's taking as many steps as it costs, and back (Steps.sw), so the
--| steps it finds to the exit are the fewest of any path (`part1Some`), and
--| finding none means there is no path (`part1None`). Whether the exit is
--| reachable is then whether there is a path (`reachableSound`,
--| `reachableComplete`).

namespace Aoc.Year2024.Day18.Proofs
import Aoc.Year2024.Day18 (..)
import Aoc.Year2024.Day18.Spec (..)
import Aoc.Common (Position)
import Std (And, Bool, Eq, Exists, Graph, List, Map, Nat, Option, Void)

--| From a safe start, the search.
theorem fromStartSafe ∀ (memory: MemorySpace)
    (safe: memory.isSafe topLeft = True):
    memory.fromStart = memory.graph.breadthFirst [topLeft] :=
  rewrite safe in rfl

--| When part 1 finds a number of steps, it is the fewest of any path.
theorem part1Some ∀ (size: Nat) (bytes: List Position) (fallen fewest: Nat)
    (answer: solvePart1 size fallen bytes = Some fewest):
    IsFewestSteps size (bytes.take fallen) fewest :=
  let memory := MemorySpace.after size bytes fallen
  let found: memory.fromStart.get memory.exit = Some fewest := answer
  match startSafe: memory.isSafe topLeft with
    | True =>
      let shortest := Graph.breadthFirstShortest memory.graph [topLeft] (unitSteps memory)
      let startSpec: isSafe size (bytes.take fallen) topLeft = True :=
        Eq.trans (Eq.sym (safeAgrees size bytes fallen topLeft)) startSafe
      Both
        (Exists.elim (And.left shortest memory.exit fewest found) (source rest =>
          Exists.elim rest (start rest2 =>
            Exists.elim rest2 (path parts =>
              let (Both isSource (Both walked costs)) := parts
              match isSource with
                | Inr none => Void.exfalso none
                | Inl same =>
                  let fromStart: topLeft = source := Eq.cong Pair.fst same
                  let startZero: 0 = start := Eq.cong Pair.snd same
                  let (Both stepsPath stepsCost) := walkSteps size bytes fallen source path memory.exit walked
                  Witness
                    (path.map Pair.fst)
                    (Both (Both startSpec (rewrite fromStart in stepsPath)) (omega [costs, startZero, stepsCost]))))))
        (steps path =>
          let (Both walked cost) := pathSteps size bytes fallen topLeft steps memory.exit (And.right path)
          Exists.elim (And.right shortest topLeft 0 (Inl rfl) _ memory.exit walked) (other both =>
            let same: other = fewest := Option.someInjective (Eq.trans (Eq.sym (And.left both)) found)
            omega [same, And.right both, cost]))

--| When part 1 finds no number of steps, there is no path.
theorem part1None ∀ (size: Nat) (bytes: List Position) (fallen: Nat)
    (answer: solvePart1 size fallen bytes = None) (steps: List Position)
    (path: IsPath size (bytes.take fallen) steps):
    Void :=
  let memory := MemorySpace.after size bytes fallen
  let startSafe: memory.isSafe topLeft = True := Eq.trans (safeAgrees size bytes fallen topLeft) (And.left path)
  let missing: (memory.graph.breadthFirst [topLeft]).get memory.exit = None :=
    Eq.trans (Eq.cong (settled => settled.get memory.exit) (Eq.sym (fromStartSafe memory startSafe))) answer
  let shortest := Graph.breadthFirstShortest memory.graph [topLeft] (unitSteps memory)
  let (Both walked cost) := pathSteps size bytes fallen topLeft steps memory.exit (And.right path)
  Exists.elim (And.right shortest topLeft 0 (Inl rfl) _ memory.exit walked) (other both =>
    Option.noneNotSome other (Eq.trans (Eq.sym missing) (And.left both)))

--| Reachable means there is a path...
theorem reachableSound ∀ (size: Nat) (bytes: List Position) (fallen: Nat)
    (open: reachable size bytes fallen = True):
    HasPath size bytes fallen :=
  let some: (solvePart1 size fallen bytes).isSome = True := open
  match answer: solvePart1 size fallen bytes with
    | Some fewest =>
      Exists.elim (And.left (part1Some size bytes fallen fewest answer)) (steps both => Witness steps (And.left both))

--| ...and a path means reachable.
theorem reachableComplete ∀ (size: Nat) (bytes: List Position) (fallen: Nat)
    (has: HasPath size bytes fallen):
    reachable size bytes fallen = True :=
  let some: (solvePart1 size fallen bytes).isSome = True := match answer: solvePart1 size fallen bytes with
    | Some fewest => rfl
    | None => Exists.elim has (steps path => Void.exfalso (part1None size bytes fallen answer steps path))
  some
