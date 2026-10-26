-- Proofs about `generateLevel` itself, under the seeded handler, for every
-- seed. The generator draws its numbers first (`drawMore`) and then plans
-- the level purely (`planFrom`), so the handler's part is one fact proved by
-- induction on the count (`seededDrawMore`: the seeded generator hands
-- `planFrom` the numbers `seededNumbers` lists), and everything else is
-- about `planFrom` on any numbers at all.
--
-- `generateLevel`, `layOut` and `drawCount` are opaque, so these proofs
-- never run the generator on an unknown seed or draw an unknown level's
-- terrain; only `generatedReachable` unfolds `generateLevel`, one step, to
-- see that it is `planFrom` of the draws.

namespace Rogue.Proofs
import Rogue (..)
import Std (Eq, List, Nat)

-- A roll is below its bound: `roll most` under the seeded handler is at
-- most `most`. (Under any handler, `roll most` is a remainder by
-- `Succ most`; `seeded` is the handler the game and its tests use.)
theorem rollBelow (seed: Nat) (most: Nat): seeded seed (() => roll most) < Succ most := Nat.modLt (lcg seed / 65536) (Succ most)

-- The numbers `drawMore drawn count` gets from the generator seeded with
-- `seed`, after `drawn`.
def seededNumbers (seed: Nat) (drawn: List Nat): Nat → List Nat
  | 0 => drawn
  | Succ remaining => seededNumbers (lcg seed) (drawn ++ [lcg seed / 65536]) remaining

-- Drawing under the seeded handler, then finishing purely, is finishing
-- with the numbers `seededNumbers` lists.
theorem seededDrawMore (finish: List Nat → b):
    (count: Nat) → (seed: Nat) → (drawn: List Nat) → seeded seed (() => finish (drawMore drawn count)) = finish (seededNumbers seed drawn count)
  | Zero, seed, drawn => rfl
  | Succ count, seed, drawn => seededDrawMore finish count (lcg seed) (drawn ++ [lcg seed / 65536])

-- The same with two pure steps after the drawing. (Not a consequence of
-- the one above: `next (first (drawMore …))` is a sequence of two steps,
-- and joining them into one needs `Effect.bindAssoc`, which uses an axiom.)
theorem seededDrawMoreThen (first: List Nat → b) (next: b → c):
    (count: Nat) → (seed: Nat) → (drawn: List Nat) → seeded seed (() => next (first (drawMore drawn count))) = next (first (seededNumbers seed drawn count))
  | Zero, seed, drawn => rfl
  | Succ count, seed, drawn => seededDrawMoreThen first next count (lcg seed) (drawn ++ [lcg seed / 65536])

-- So the level at `depth` from `seed` is planned from those numbers.
theorem generatedPlan (seed: Nat) (depth: Nat): seeded seed (() => generateLevel depth) = planFrom depth (seededNumbers seed [] (drawCount depth))
    unfolding generateLevel
:=
  seededDrawMore (planFrom depth) (drawCount depth) seed []

-- On a level planned from any numbers, the way on can be walked to from
-- the start: the entrance and exit numbers are remainders by 6.
theorem planReachable (depth: Nat) (numbers: List Nat):
    Reachable (planFrom depth numbers).level (planFrom depth numbers).level.start (planFrom depth numbers).level.goal :=
  goalReachable depth (roomsFrom numbers) (entranceFrom numbers) (exitFrom numbers) (extraFrom numbers)
    (Nat.modLt (numbers.getOr 0 (6 * roomDraws)) 6)
    (Nat.modLt (entranceFrom numbers + 1 + rollAt numbers (6 * roomDraws + 1) 4) 6)

-- Whatever a planned level is true of, every generated level is, for
-- every seed and depth.
theorem generatedHolds (property: Plan → Prop) (planned: (depth: Nat) → (numbers: List Nat) → property (planFrom depth numbers))
    (seed: Nat) (depth: Nat): property (seeded seed (() => generateLevel depth)) :=
  J (plan same => property plan) (planned depth (seededNumbers seed [] (drawCount depth))) (Eq.sym (generatedPlan seed depth))

-- So on every level the game generates, for every seed and depth, the way
-- on can be walked to from the start.
theorem generatedReachable (seed: Nat) (depth: Nat):
    Reachable (seeded seed (() => generateLevel depth)).level (seeded seed (() => generateLevel depth)).level.start (seeded seed (() => generateLevel depth)).level.goal :=
  generatedHolds (plan => Reachable plan.level plan.level.start plan.level.goal) planReachable seed depth

-- A new game, as the real program starts it under the seeded handler, is
-- `startingState` of the level generated from that seed.
theorem seededNewGame (seed: Nat): seeded seed (() => newGame()) = startingState (seeded seed (() => generateLevel 1))
    unfolding generateLevel
:=
  Eq.trans (seededDrawMoreThen (planFrom 1) startingState (drawCount 1) seed []) (Eq.cong startingState (Eq.sym (generatedPlan seed 1)))
