-- The three invariants together: a game starts valid, and every turn keeps
-- it valid, whatever the seed and the command. By induction, so does every
-- game, however long.

namespace Rogue.Proofs
import Rogue (..)

type Valid (state: State): Prop = {
  outOfWalls: isWall state.player = False,
  atMost: state.hitPoints ≤ maxHitPoints,
  clear: Clear state.player state.monsters
}

theorem initialValid: Valid initialState := { outOfWalls = rfl, atMost = rfl, clear = rfl }

theorem stepValid (seed: Nat) (state: State) (command: Command) (valid: Valid state):
    Valid (seeded seed (() => step state command)) := {
      outOfWalls = stepOutOfWalls seed state command valid.outOfWalls,
      atMost = stepAtMost seed state command valid.atMost,
      clear = stepClear seed state command valid.clear
    }
