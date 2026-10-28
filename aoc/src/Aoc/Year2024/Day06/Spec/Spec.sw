-- Day 6 as the puzzle states it, over the program's `Lab.step`, which is
-- the patrol protocol: "If there is something directly in front of you, turn
-- right 90 degrees. Otherwise, take a step forward." The proofs (Proofs/)
-- show the program computes these, for every lab whose guard starts on the
-- map.

namespace Aoc.Year2024.Day06.Spec
import Aoc.Year2024.Day06 (..)
import Std (Bool, Iff, List, Nat, Option, Set)

-- The guard after `steps` more steps from `guard`: `None` once she has left
-- the mapped area.
def walk (lab: Lab) (guard: Option Guard): (steps: Nat) → Option Guard
  | Zero => guard
  | Succ steps => walk lab (guard.flatMap lab.step) steps

-- The guard `steps` steps after the patrol begins.
def after (lab: Lab) (steps: Nat): Option Guard := walk lab (Some lab.startGuard) steps

-- "The guard will get stuck in a loop": she never leaves the mapped area.
def Loops (lab: Lab): Prop := (steps: Nat) → Not (after lab steps = None)

-- Where the guard stands over her first `steps` steps from `guard`, in
-- order, fewer if she leaves sooner.
def route (lab: Lab) (guard: Option Guard): (steps: Nat) → List Position
  | Zero => Nil
  | Succ steps =>
    match guard with
      | None => Nil
      | Some here => Cons here.position (route lab (lab.step here) steps)

-- "How many distinct positions will the guard visit before leaving the
-- mapped area?", given a number of steps by which she has left.
def distinctPositions (lab: Lab) (steps: Nat): Nat := (Set.fromList (route lab (Some lab.startGuard) steps)).size

-- On the mapped area.
def onMap (lab: Lab) (position: Position): Bool := position.row < lab.height && position.column < lab.width

-- Every position on the mapped area.
def positions (lab: Lab): List Position :=
  List.range lab.height |> .flatMap (row => List.range lab.width |> .map (column => ({ row, column }: Position)))

-- "All of the possible positions for such an obstruction": a new one, on
-- the map, not "at the guard's starting position", where "the guard will get
-- stuck in a loop". `trapped` decides `Loops` for the lab with an
-- obstruction there, so any such decision gives the same set.
def trapPositions (lab: Lab) (trapped: Position → Bool): Set Position :=
  Set.fromList (positions lab)
    |> .filter (position => position != lab.start && !lab.obstructions.contains position && trapped position)

-- `trapped` decides whether the guard loops with an obstruction added at
-- each position.
def Decides (lab: Lab) (trapped: Position → Bool): Prop :=
  (position: Position) → Iff (trapped position = True) (Loops (lab.withObstruction position))
