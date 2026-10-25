-- Hit points never exceed the maximum after a turn (`stepAtMost`): a potion
-- heals no further than the maximum, and blows only take hit points away.

namespace Rogue.Proofs
import Rogue (..)
import Std (Decidable, Eq, List, Nat)

theorem healedAtMost (hitPoints: Nat): healed hitPoints ≤ maxHitPoints :=
  match fits: Nat.leq (hitPoints + potionStrength) maxHitPoints with
    | True => fits
    | False => rfl

theorem enterAtMost (state: State) (target: Position) (atMost: state.hitPoints ≤ maxHitPoints):
    (enter state target).hitPoints ≤ maxHitPoints :=
  match potion: Decidable.toBool (List.decMem target state.potions) with
    | True => healedAtMost state.hitPoints
    | False => atMost

theorem monstersTurnAtMost (dice: Dice) (state: State) (atMost: state.hitPoints ≤ maxHitPoints):
    (monstersTurn dice state).hitPoints ≤ maxHitPoints :=
  match stairs: isStairs state.player with
    | True => atMost
    | False => omega

theorem playerMovesAtMost (dice: Dice) (state: State) (direction: Direction) (atMost: state.hitPoints ≤ maxHitPoints):
    (playerMoves dice state direction).hitPoints ≤ maxHitPoints :=
  match found: monsterAt (state.player.toward direction) state.monsters with
    | Some monster => atMost
    | None =>
      match wall: isWall (state.player.toward direction) with
        | True => atMost
        | False => enterAtMost state (state.player.toward direction) atMost

theorem resolveAtMost (dice: Dice) (state: State) (command: Command) (atMost: state.hitPoints ≤ maxHitPoints):
    (resolve dice state command).hitPoints ≤ maxHitPoints :=
  match phase: state.phase with
    | Playing =>
      match command with
        | Quit => atMost
        | Wait => monstersTurnAtMost dice { state | message = "You wait." } atMost
        | Move direction => monstersTurnAtMost dice (playerMoves dice state direction) (playerMovesAtMost dice state direction atMost)
    | Escaped => atMost
    | Died => atMost
    | GaveUp => atMost

-- Hit points never exceed the maximum after a turn, whatever the seed.
theorem stepAtMost (seed: Nat) (state: State) (command: Command) (atMost: state.hitPoints ≤ maxHitPoints):
    (seeded seed (() => step state command)).hitPoints ≤ maxHitPoints :=
  resolveAtMost { seed = lcg seed / 65536 } state command atMost
