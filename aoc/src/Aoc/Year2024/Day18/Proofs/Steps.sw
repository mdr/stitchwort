-- The program's moves are the puzzle's steps (`moveAgrees`), and its
-- graph's edges are those moves, each costing one (`edgesSound`,
-- `edgesComplete`). Walks join (`walkAppend`), and keep going with fewer
-- bytes fallen (`walkFewer`).

namespace Aoc.Year2024.Day18.Proofs
import Aoc.Year2024.Day18 (..)
import Aoc.Year2024.Day18.Spec (..)
import Aoc.Year2024.Day16.Proofs (anyMember)
import Std (And, Bool, Eq, Exists, List, Map, Nat, Option, Set, Void)

-- The program's corrupted set holds the bytes fallen.
theorem safeAgrees (size: Nat) (bytes: List Position) (fallen: Nat) (position: Position):
    (MemorySpace.after size bytes fallen).isSafe position = isSafe size (bytes.take fallen) position :=
  rewrite Set.containsFromList position (bytes.take fallen) in
    rewrite List.anyCong (bytes.take fallen) (other => Map.Spec.sameKey position other) (other => other == position)
      (other => Map.Spec.sameKeyDecide position other) in rfl

-- The program's move is the puzzle's step.
theorem moveAgrees (size: Nat) (bytes: List Position) (fallen: Nat) (position: Position) (direction: Direction):
    (MemorySpace.after size bytes fallen).move position direction = stepTo size (bytes.take fallen) position direction :=
  match stepped: position.step direction with
    | Some next => rewrite safeAgrees size bytes fallen next in rfl
    | None => rfl

-- A step taken is a neighbour, and safe.
theorem stepToCases (size: Nat) (fallen: List Position) (position: Position) (direction: Direction) (next: Position)
    (moved: stepTo size fallen position direction = Some next): And (position.step direction = Some next) (isSafe size fallen next = True) :=
  match stepped: position.step direction with
    | None => Void.exfalso (Option.noneNotSome next moved)
    | Some found =>
      match safe: isSafe size fallen found with
        | False => Void.exfalso (Option.noneNotSome next moved)
        | True => rewrite <- Option.someInjective _ _ moved in Both rfl safe

-- A safe neighbour can be stepped to.
theorem stepToIntro (size: Nat) (fallen: List Position) (position: Position) (direction: Direction) (next: Position)
    (stepped: position.step direction = Some next) (safe: isSafe size fallen next = True): stepTo size fallen position direction = Some next :=
  rewrite stepped, safe in rfl

theorem directionsComplete: (direction: Direction) → direction ∈ directions
  | Up => Inl rfl
  | Down => Inr (Inl rfl)
  | Left => Inr (Inr (Inl rfl))
  | Right => Inr (Inr (Inr (Inl rfl)))

-- Each edge is a move, costing one.
theorem edgesSound (memory: MemorySpace) (position: Position) (next: Position) (weight: Nat) (edge: (next, weight) ∈ memory.edges position):
    And (Exists Direction (direction => memory.move position direction = Some next)) (weight = 1) :=
  let found := List.memFilterMapElim (direction => memory.move position direction |> .map (other => (other, 1))) (next, weight) directions edge
  Exists.elim (anyMember (direction => (memory.move position direction |> .map (other => (other, 1))) = Some (next, weight)) directions found)
    (direction both =>
      match moved: memory.move position direction with
        | None => Void.exfalso (Option.noneNotSome (next, weight) (And.right both))
        | Some other =>
          let same := Option.someInjective _ _ (And.right both)
          Both (Witness direction (Eq.trans moved (Eq.cong Some (Eq.cong Pair.fst same)))) (Eq.sym (Eq.cong Pair.snd same)))

-- Each move is an edge.
theorem edgesComplete (memory: MemorySpace) (position: Position) (direction: Direction) (next: Position)
    (moved: memory.move position direction = Some next): (next, 1) ∈ memory.edges position :=
  List.memFilterMapIntro (way => memory.move position way |> .map (other => (other, 1))) direction (next, 1) directions (directionsComplete direction)
    (rewrite moved in rfl)

-- Moves lead to safe positions.
theorem moveSafe (memory: MemorySpace) (position: Position) (direction: Direction) (next: Position)
    (moved: memory.move position direction = Some next): memory.isSafe next = True :=
  match stepped: position.step direction with
    | None => Void.exfalso (Option.noneNotSome next moved)
    | Some found =>
      match safe: memory.isSafe found with
        | False => Void.exfalso (Option.noneNotSome next moved)
        | True => rewrite <- Option.someInjective _ _ moved in safe

-- After a first step, the rest of the walk.
theorem walkCons (size: Nat) (fallen: List Position) (position: Position) (direction: Direction) (next: Position)
    (moved: stepTo size fallen position direction = Some next) (rest: List Direction):
    walk size fallen position (Cons direction rest) = walk size fallen next rest :=
  rewrite moved in rfl

-- Steps then more steps: the more steps from where the first left off.
theorem walkAppend (size: Nat) (fallen: List Position) (more: List Direction): (position: Position) → (steps: List Direction) → (middle: Position) →
    walk size fallen position steps = Some middle → walk size fallen position (steps ++ more) = walk size fallen middle more
  | position, Nil, middle, ended => rewrite Option.someInjective _ _ ended in rfl
  | position, Cons direction rest, middle, ended =>
    match moved: stepTo size fallen position direction with
      | None => Void.exfalso (Option.noneNotSome middle ended)
      | Some next => walkAppend size fallen more next rest middle ended

-- Steps, then one more.
theorem walkSnoc (size: Nat) (fallen: List Position) (position: Position) (steps: List Direction) (middle: Position)
    (ended: walk size fallen position steps = Some middle) (direction: Direction) (next: Position)
    (moved: stepTo size fallen middle direction = Some next): walk size fallen position (steps ++ [direction]) = Some next :=
  Eq.trans (walkAppend size fallen [direction] position steps middle ended) (walkCons size fallen middle direction next moved Nil)

-- A position safe with more bytes fallen is safe with fewer.
theorem safeFewer (size: Nat) (bytes: List Position) (fewer: Nat) (more: Nat) (le: fewer ≤ more) (position: Position)
    (safe: isSafe size (bytes.take more) position = True): isSafe size (bytes.take fewer) position = True :=
  let xInside := Bool.andLeft _ _ safe
  let yInside := Bool.andLeft _ _ (Bool.andRight _ _ safe)
  let clear := Bool.andRight _ _ (Bool.andRight _ _ safe)
  match there: (bytes.take fewer).contains position with
    | True =>
      let worse := containsTakeMono position bytes fewer more le there
      rewrite worse at clear in Void.exfalso (Bool.falseNotTrue clear)
    | False => Bool.andIntro _ _ xInside (Bool.andIntro _ _ yInside rfl)

-- A walk with more bytes fallen is a walk with fewer.
theorem walkFewer (size: Nat) (bytes: List Position) (fewer: Nat) (more: Nat) (le: fewer ≤ more): (position: Position) →
    (steps: List Direction) → (last: Position) → walk size (bytes.take more) position steps = Some last →
    walk size (bytes.take fewer) position steps = Some last
  | position, Nil, last, ended => ended
  | position, Cons direction rest, last, ended =>
    match moved: stepTo size (bytes.take more) position direction with
      | None => Void.exfalso (Option.noneNotSome last ended)
      | Some next =>
        let (Both stepped safe) := stepToCases size (bytes.take more) position direction next moved
        rewrite walkCons size (bytes.take fewer) position direction next
          (stepToIntro size (bytes.take fewer) position direction next stepped (safeFewer size bytes fewer more le next safe)) rest in
          walkFewer size bytes fewer more le next rest last ended
