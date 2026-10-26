-- Hit points never exceed the maximum after a turn (`stepAtMost`): a potion
-- heals no further than the maximum, blows only take hit points away, and
-- nothing else changes them.

namespace Rogue.Proofs
import Rogue (..)
import Std (Eq, Nat)

theorem healedAtMost (hitPoints: Nat): healed hitPoints ≤ maxHitPoints :=
  match fits: Nat.leq (hitPoints + potionStrength) maxHitPoints with
    | True => fits
    | False => rfl

theorem monstersTurnAtMost (dice: Dice) (state: State) (atMost: state.hitPoints ≤ maxHitPoints):
    (monstersTurn dice state).hitPoints ≤ maxHitPoints :=
  match phase: state.phase with
    | Playing => omega
    | Won => atMost
    | Died => atMost
    | GaveUp => atMost

theorem playerMovesAtMost (dice: Dice) (state: State) (direction: Direction) (atMost: state.hitPoints ≤ maxHitPoints):
    (playerMoves dice state direction).hitPoints ≤ maxHitPoints :=
  match found: monsterAt (state.player.toward direction) state.monsters with
    | Some monster => atMost
    | None =>
      match wall: isWall state.level (state.player.toward direction) with
        | True => atMost
        | False => rewrite enterHitPoints state (state.player.toward direction) in atMost

theorem descendAtMost (dice: Dice) (state: State) (atMost: state.hitPoints ≤ maxHitPoints): (descend dice state).hitPoints ≤ maxHitPoints :=
  atMost

theorem resolveAtMost (dice: Dice) (state: State) (command: Command) (atMost: state.hitPoints ≤ maxHitPoints):
    (resolve dice state command).hitPoints ≤ maxHitPoints :=
  match phase: state.phase with
    | Playing =>
      match command with
        | Quit => atMost
        | Wait => monstersTurnAtMost dice { state | message = "You wait." } atMost
        | Move direction => monstersTurnAtMost dice (playerMoves dice state direction) (playerMovesAtMost dice state direction atMost)
        | Drink =>
          match none: state.potions == 0 with
            | True => atMost
            | False => monstersTurnAtMost dice (drink state) (healedAtMost state.hitPoints)
        | Descend =>
          match stairs: isStairs state.level state.player with
            | True => descendAtMost dice state atMost
            | False => atMost
    | Won => atMost
    | Died => atMost
    | GaveUp => atMost

-- Hit points never exceed the maximum after a turn, whatever the seed.
theorem stepAtMost (seed: Nat) (state: State) (command: Command) (atMost: state.hitPoints ≤ maxHitPoints):
    (seeded seed (() => step state command)).hitPoints ≤ maxHitPoints :=
  resolveAtMost { seed = lcg seed / 65536 } state command atMost
