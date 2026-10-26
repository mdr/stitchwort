-- The invariants together: a game starts valid, every turn keeps it valid,
-- whatever the seed and the command, and so does arriving on any level the
-- generator could make. So does every game, however long (`replayValid`,
-- Game.sw).

namespace Rogue.Proofs
import Rogue (..)

type Valid (state: State): Prop = {
  outOfWalls: isWall state.level state.player = False,
  atMost: state.hitPoints ≤ maxHitPoints,
  clear: Clear state.player state.monsters,
  onFloor: OnFloor state.level state.monsters,
  apart: Apart state.monsters
}

-- Arriving on a level, whatever the generator planned, is valid.
theorem arriveValid (state: State) (plan: Plan) (atMost: state.hitPoints ≤ maxHitPoints): Valid (arrive state plan) := {
  outOfWalls = startOnFloor plan.level,
  atMost = atMost,
  clear = placeMonstersClear plan.level plan.level.start [] plan.monsters rfl,
  onFloor = placeMonstersOnFloor plan.level plan.level.start [] plan.monsters Trivial,
  apart = placeMonstersApart plan.level plan.level.start [] plan.monsters Trivial
}

-- So every new game starts valid.
theorem startingValid (plan: Plan): Valid (startingState plan) := arriveValid (freshState plan) plan rfl

-- A turn with any dice keeps the state valid.
theorem resolveValid (dice: Dice) (state: State) (command: Command) (valid: Valid state): Valid (resolve dice state command) := {
  outOfWalls = resolveOutOfWalls dice state command valid.outOfWalls,
  atMost = resolveAtMost dice state command valid.atMost,
  clear = resolveClear dice state command valid.clear,
  onFloor = resolveOnFloor dice state command valid.onFloor,
  apart = resolveApart dice state command valid.apart
}

theorem stepValid (seed: Nat) (state: State) (command: Command) (valid: Valid state):
    Valid (seeded seed (() => step state command)) := {
      outOfWalls = stepOutOfWalls seed state command valid.outOfWalls,
      atMost = stepAtMost seed state command valid.atMost,
      clear = stepClear seed state command valid.clear,
      onFloor = stepOnFloor seed state command valid.onFloor,
      apart = stepApart seed state command valid.apart
    }
