-- The player is never inside a wall after a turn (`stepOutOfWalls`): the
-- player only moves onto a cell that `isWall` has just said isn't one, or
-- down the stairs to the start of a new level, which is floor on every
-- level (Level.sw); and nothing else in a turn moves them.

namespace Rogue.Proofs
import Rogue (..)
import Std (Eq)

theorem playerMovesOutOfWalls (dice: Dice) (state: State) (direction: Direction) (inside: isWall state.level state.player = False):
    isWall (playerMoves dice state direction).level (playerMoves dice state direction).player = False :=
  match found: monsterAt (state.player.toward direction) state.monsters with
    | Some monster => inside
    | None =>
      match wall: isWall state.level (state.player.toward direction) with
        | True => inside
        | False =>
          let target := state.player.toward direction
          rewrite enterLevel state target, enterPlayer state target in wall

theorem monstersTurnOutOfWalls (dice: Dice) (state: State) (inside: isWall state.level state.player = False):
    isWall (monstersTurn dice state).level (monstersTurn dice state).player = False :=
  rewrite monstersTurnLevel dice state, monstersTurnPlayer dice state in inside

theorem descendOutOfWalls (dice: Dice) (state: State) (inside: isWall state.level state.player = False):
    isWall (descend dice state).level (descend dice state).player = False :=
  startOnFloor (seeded dice.seed (() => generateLevel (state.level.depth + 1))).level

theorem resolveOutOfWalls (dice: Dice) (state: State) (command: Command) (inside: isWall state.level state.player = False):
    isWall (resolve dice state command).level (resolve dice state command).player = False :=
  match phase: state.phase with
    | Playing =>
      match command with
        | Quit => inside
        | Wait => monstersTurnOutOfWalls dice { state | message = "You wait." } inside
        | Move direction => monstersTurnOutOfWalls dice (playerMoves dice state direction) (playerMovesOutOfWalls dice state direction inside)
        | Drink =>
          match none: state.potions == 0 with
            | True => inside
            | False => monstersTurnOutOfWalls dice (drink state) inside
        | Descend =>
          match stairs: isStairs state.level state.player with
            | True => descendOutOfWalls dice state inside
            | False => inside
    | Won => inside
    | Died => inside
    | GaveUp => inside

-- The player is never inside a wall after a turn, whatever the seed.
theorem stepOutOfWalls (seed: Nat) (state: State) (command: Command) (inside: isWall state.level state.player = False):
    isWall (seeded seed (() => step state command)).level (seeded seed (() => step state command)).player = False :=
  resolveOutOfWalls { seed = lcg seed / 65536 } state command inside
