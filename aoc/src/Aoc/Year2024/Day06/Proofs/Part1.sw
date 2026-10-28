-- Part 1 proved: for a guard who starts on the map, the program counts the
-- distinct positions of her route, for any number of steps by which she has
-- left (`part1Correct`), and gives `None` exactly when she loops.

namespace Aoc.Year2024.Day06.Proofs
import Aoc.Year2024.Day06 (..)
import Aoc.Year2024.Day06.Spec (..)
import Std (Eq, List, Nat, Not, Option, Set, Void)

-- Off the map, there is no route.
theorem routeNone (lab: Lab): (steps: Nat) → route lab None steps = Nil
  | Zero => rfl
  | Succ steps => rfl

-- Once she has left, more steps add nothing to the route.
theorem routeAfterGone (lab: Lab): (steps: Nat) → (guard: Option Guard) → walk lab guard steps = None → (more: Nat) → steps ≤ more →
    route lab guard more = route lab guard steps
  | Zero, guard, gone, more, le => rewrite gone, routeNone lab more in rfl
  | Succ steps, None, gone, more, le => rewrite routeNone lab more in rfl
  | Succ steps, Some here, gone, Zero, le => omega
  | Succ steps, Some here, gone, Succ more, le =>
    rewrite routeAfterGone lab steps (lab.step here) gone more le in rfl

-- With budget enough to leave, the walk collects the route's positions.
theorem patrolFromRoute (lab: Lab): (budget: Nat) → (guard: Guard) → (visited: Set Position) → walk lab (Some guard) budget = None →
    lab.patrolFrom guard visited budget = Some ((route lab (Some guard) budget).foldLeft visited (set key => set.insert key))
  | Zero, guard, visited, gone => Void.exfalso (Option.someNotNone guard gone)
  | Succ budget, guard, visited, gone =>
    match stepped: lab.step guard with
      | None => rewrite routeNone lab budget in rfl
      | Some next => patrolFromRoute lab budget next (visited.insert guard.position) gone

-- A walk that collects anything leaves within its budget.
theorem patrolFromGone (lab: Lab): (budget: Nat) → (guard: Guard) → (visited: Set Position) → (found: Set Position) →
    lab.patrolFrom guard visited budget = Some found → walk lab (Some guard) budget = None
  | Zero, guard, visited, found, collected => Void.exfalso (Option.noneNotSome found collected)
  | Succ budget, guard, visited, found, collected =>
    match stepped: lab.step guard with
      | None => walkNone lab budget
      | Some next => patrolFromGone lab budget next (visited.insert guard.position) found collected

-- A guard who leaves at all leaves within the budget.
theorem goneInBudget (lab: Lab) (inside: onMap lab lab.start = True) (steps: Nat) (gone: after lab steps = None):
    after lab lab.stateCount = None :=
  match still: after lab lab.stateCount with
    | None => rfl
    | Some guard => Void.exfalso (budgetEnough lab inside (rewrite still in Option.someNotNone guard) steps gone)

-- The patrol is the set of the route's positions.
theorem patrolRoute (lab: Lab) (inside: onMap lab lab.start = True) (steps: Nat) (gone: after lab steps = None):
    lab.patrol = Some (Set.fromList (route lab (Some lab.startGuard) steps)) :=
  let inBudget := goneInBudget lab inside steps gone
  let sameRoute: route lab (Some lab.startGuard) lab.stateCount = route lab (Some lab.startGuard) steps :=
    match early: Nat.leq steps lab.stateCount with
      | True => routeAfterGone lab steps (Some lab.startGuard) gone lab.stateCount early
      | False => Eq.sym (routeAfterGone lab lab.stateCount (Some lab.startGuard) inBudget steps omega)
  rewrite patrolFromRoute lab lab.stateCount lab.startGuard Set.empty inBudget, sameRoute in rfl

-- Part 1 counts the distinct positions the guard visits before leaving.
theorem part1Correct (lab: Lab) (inside: onMap lab lab.start = True) (steps: Nat) (gone: after lab steps = None):
    solvePart1 lab = Some (distinctPositions lab steps) :=
  rewrite patrolRoute lab inside steps gone in rfl

-- And gives no answer when she loops.
theorem part1Loops (lab: Lab) (loops: Loops lab): solvePart1 lab = None :=
  match patrolled: lab.patrol with
    | None => rfl
    | Some found => Void.exfalso (loops lab.stateCount (patrolFromGone lab lab.stateCount lab.startGuard Set.empty found patrolled))
