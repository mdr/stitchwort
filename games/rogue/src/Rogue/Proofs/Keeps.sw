-- What each part of a turn leaves alone: the monsters' turn doesn't move
-- the player or change the level, and walking onto a cell (and picking up
-- what's there) changes neither the level, the monsters nor hit points.

namespace Rogue.Proofs
import Rogue (..)
import Std (Eq, List, Option)

theorem monstersTurnPlayer (dice: Dice) (state: State): (monstersTurn dice state).player = state.player :=
  match phase: state.phase with
    | Playing => rfl
    | Won => rfl
    | Died => rfl
    | GaveUp => rfl

theorem monstersTurnLevel (dice: Dice) (state: State): (monstersTurn dice state).level = state.level :=
  match phase: state.phase with
    | Playing => rfl
    | Won => rfl
    | Died => rfl
    | GaveUp => rfl

theorem pickUpPlayer (state: State) (loot: Loot): (pickUp state loot).player = state.player :=
  match loot with
    | Potion => rfl
    | Sword => rfl
    | Amulet => rfl

theorem pickUpLevel (state: State) (loot: Loot): (pickUp state loot).level = state.level :=
  match loot with
    | Potion => rfl
    | Sword => rfl
    | Amulet => rfl

theorem pickUpMonsters (state: State) (loot: Loot): (pickUp state loot).monsters = state.monsters :=
  match loot with
    | Potion => rfl
    | Sword => rfl
    | Amulet => rfl

theorem pickUpHitPoints (state: State) (loot: Loot): (pickUp state loot).hitPoints = state.hitPoints :=
  match loot with
    | Potion => rfl
    | Sword => rfl
    | Amulet => rfl

theorem enterPlayer (state: State) (target: Position): (enter state target).player = target :=
  match found: itemAt target state.items with
    | Some item => pickUpPlayer { state | player = target, message = "", items = state.items.filter (other => other.position ≠ target) } item.loot
    | None => rfl

theorem enterLevel (state: State) (target: Position): (enter state target).level = state.level :=
  match found: itemAt target state.items with
    | Some item => pickUpLevel { state | player = target, message = "", items = state.items.filter (other => other.position ≠ target) } item.loot
    | None => rfl

theorem enterMonsters (state: State) (target: Position): (enter state target).monsters = state.monsters :=
  match found: itemAt target state.items with
    | Some item => pickUpMonsters { state | player = target, message = "", items = state.items.filter (other => other.position ≠ target) } item.loot
    | None => rfl

theorem enterHitPoints (state: State) (target: Position): (enter state target).hitPoints = state.hitPoints :=
  match found: itemAt target state.items with
    | Some item => pickUpHitPoints { state | player = target, message = "", items = state.items.filter (other => other.position ≠ target) } item.loot
    | None => rfl
