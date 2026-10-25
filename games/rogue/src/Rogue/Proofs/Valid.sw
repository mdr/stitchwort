-- The invariants together: a game starts valid, every turn keeps it valid,
-- whatever the seed and the command, and so does arriving on any level the
-- generator could make. By induction, so does every game, however long.

namespace Rogue.Proofs
import Rogue (..)

type Valid (state: State): Prop = {
  outOfWalls: isWall state.level state.player = False,
  atMost: state.hitPoints ≤ maxHitPoints,
  clear: Clear state.player state.monsters,
  onFloor: OnFloor state.level state.monsters
}

-- Arriving on a level, whatever the generator planned, is valid.
theorem arriveValid (state: State) (plan: Plan) (atMost: state.hitPoints ≤ maxHitPoints): Valid (arrive state plan) := {
  outOfWalls = startOnFloor plan.level,
  atMost = atMost,
  clear = placeMonstersClear plan.level plan.level.start [] plan.monsters rfl,
  onFloor = placeMonstersOnFloor plan.level plan.level.start [] plan.monsters Trivial
}

-- So every new game starts valid.
theorem startingValid (plan: Plan) (deeper: List Plan): Valid (startingState plan deeper) := arriveValid (freshState plan deeper) plan rfl

theorem stepValid (seed: Nat) (state: State) (command: Command) (valid: Valid state):
    Valid (seeded seed (() => step state command)) := {
      outOfWalls = stepOutOfWalls seed state command valid.outOfWalls,
      atMost = stepAtMost seed state command valid.atMost,
      clear = stepClear seed state command valid.clear,
      onFloor = stepOnFloor seed state command valid.onFloor
    }
