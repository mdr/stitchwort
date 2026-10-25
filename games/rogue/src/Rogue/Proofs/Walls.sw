-- The player is never inside a wall after a turn (`stepOutOfWalls`): the
-- player only moves onto a cell that `isWall` has just said isn't one, and
-- nothing else in a turn moves them.

namespace Rogue.Proofs
import Rogue (..)
import Std (Eq)

theorem monstersTurnPlayer (dice: Dice) (state: State): (monstersTurn dice state).player = state.player :=
  match stairs: isStairs state.player with
    | True => rfl
    | False => rfl

theorem enterPlayer (state: State) (target: Position): (enter state target).player = target :=
  match potion: state.potions.any (== target) with
    | True => rfl
    | False => rfl

theorem playerMovesOutOfWalls (dice: Dice) (state: State) (direction: Direction) (inside: isWall state.player = False):
    isWall (playerMoves dice state direction).player = False :=
  match found: monsterAt (state.player.toward direction) state.monsters with
    | Some monster => inside
    | None =>
      match wall: isWall (state.player.toward direction) with
        | True => inside
        | False => Eq.trans (Eq.cong isWall (enterPlayer state (state.player.toward direction))) wall

theorem resolveOutOfWalls (dice: Dice) (state: State) (command: Command) (inside: isWall state.player = False):
    isWall (resolve dice state command).player = False :=
  match phase: state.phase with
    | Playing =>
      match command with
        | Quit => inside
        | Wait => Eq.trans (Eq.cong isWall (monstersTurnPlayer dice { state | message = "You wait." })) inside
        | Move direction => Eq.trans (Eq.cong isWall (monstersTurnPlayer dice (playerMoves dice state direction))) (playerMovesOutOfWalls dice state direction inside)
    | Escaped => inside
    | Died => inside
    | GaveUp => inside

-- The player is never inside a wall after a turn, whatever the seed.
theorem stepOutOfWalls (seed: Nat) (state: State) (command: Command) (inside: isWall state.player = False):
    isWall (seeded seed (() => step state command)).player = False :=
  resolveOutOfWalls { seed = lcg seed / 65536 } state command inside
