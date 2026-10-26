-- No monster stands in a wall after a turn (`stepOnFloor`): a blow changes
-- monsters without moving them, each monster either stays put or moves to
-- a cell `pickFree` has checked isn't a wall, and a new level's monsters
-- are placed by `pickFree` too (Level.sw).

namespace Rogue.Proofs
import Rogue (..)
import Std (Eq, List, Option, Void)

-- No monster stands in a wall of the level.
def OnFloor (level: Level) (monsters: List Monster): Prop := List.All (monster => isWall level monster.position = False) monsters

-- A monster never chooses a wall.
theorem pickFreeOnFloor (level: Level) (player: Position) (others: List Monster):
    (choices: List Position) → (destination: Position) → pickFree level choices player others = Some destination → isWall level destination = False
  | [], destination, picked => Void.exfalso (Option.noneNotSome destination picked)
  | Cons choice rest, destination, picked =>
    match wall: isWall level choice with
      | True => pickFreeOnFloor level player others rest destination picked
      | False =>
        match same: choice == player with
          | True => pickFreeOnFloor level player others rest destination picked
          | False =>
            match taken: (monsterAt choice others).isSome with
              | True => pickFreeOnFloor level player others rest destination picked
              | False => rewrite <- Option.someInjective choice destination picked in wall

theorem onFloorSnoc (level: Level) (monster: Monster) (inside: isWall level monster.position = False) (monsters: List Monster) (onFloor: OnFloor level monsters):
    OnFloor level (monsters ++ [monster]) :=
  List.allAppend ((monster: Monster) => isWall level monster.position = False) monsters [monster] onFloor (Both inside Trivial)

-- Changing monsters without moving them keeps them on the floor.
theorem onFloorMap (level: Level) (change: Monster → Monster) (stays: (monster: Monster) → (change monster).position = monster.position):
    (monsters: List Monster) → OnFloor level monsters → OnFloor level (monsters.map change)
  | [], onFloor => Trivial
  | Cons first rest, Both inside others => Both (rewrite stays first in inside) (onFloorMap level change stays rest others)

-- Dropping monsters keeps the rest on the floor.
theorem onFloorFilter (level: Level) (keep: Monster → Bool):
    (monsters: List Monster) → OnFloor level monsters → OnFloor level (monsters.filter keep)
  | [], onFloor => Trivial
  | Cons first rest, Both inside others =>
    match kept: keep first with
      | True => Both inside (onFloorFilter level keep rest others)
      | False => onFloorFilter level keep rest others

-- The monsters' turn keeps them on the floor: those that attack stay
-- where they are, and those that move pick a cell that isn't a wall, or
-- stay.
theorem actAllOnFloor (dice: Dice) (level: Level) (player: Position):
    (index: Nat) → (outcome: Outcome) → (waiting: List Monster) →
    OnFloor level outcome.moved → OnFloor level waiting → OnFloor level (actAll dice level player index outcome waiting).moved
  | index, outcome, [], moved, rest => moved
  | index, outcome, Cons monster waiting, moved, Both inside rest =>
    match next: monster.position.isNextTo player with
      | True => actAllOnFloor dice level player (index + 1) (outcome.add monster _ _) waiting (onFloorSnoc level monster inside outcome.moved moved) rest
      | False =>
        match picked: pickFree level (monsterChoices dice index player monster) player (outcome.moved ++ waiting) with
          | Some destination =>
            let fresh := pickFreeOnFloor level player (outcome.moved ++ waiting) (monsterChoices dice index player monster) destination picked
            actAllOnFloor dice level player (index + 1) (outcome.add { monster | position = destination } 0 []) waiting (onFloorSnoc level { monster | position = destination } fresh outcome.moved moved) rest
          | None => actAllOnFloor dice level player (index + 1) (outcome.add { monster | position = monster.position } 0 []) waiting (onFloorSnoc level { monster | position = monster.position } inside outcome.moved moved) rest

theorem monstersTurnOnFloor (dice: Dice) (state: State) (onFloor: OnFloor state.level state.monsters):
    OnFloor (monstersTurn dice state).level (monstersTurn dice state).monsters :=
  match phase: state.phase with
    | Playing => actAllOnFloor dice state.level state.player 0 { moved = [], damage = 0, events = [] } state.monsters Trivial onFloor
    | Won => onFloor
    | Died => onFloor
    | GaveUp => onFloor

theorem playerMovesOnFloor (dice: Dice) (state: State) (direction: Direction) (onFloor: OnFloor state.level state.monsters):
    OnFloor (playerMoves dice state direction).level (playerMoves dice state direction).monsters :=
  match found: monsterAt (state.player.toward direction) state.monsters with
    | Some monster =>
      let damage := 2 + dice.upTo 0 (state.strength - 2)
      let wounded := state.monsters.map (wound monster.position damage)
      onFloorFilter state.level (other => other.hitPoints > 0) wounded
        (onFloorMap state.level (wound monster.position damage) (woundStays monster.position damage) state.monsters onFloor)
    | None =>
      match wall: isWall state.level (state.player.toward direction) with
        | True => onFloor
        | False =>
          let target := state.player.toward direction
          rewrite enterLevel state target, enterMonsters state target in onFloor

theorem descendOnFloor (dice: Dice) (state: State) (onFloor: OnFloor state.level state.monsters):
    OnFloor (descend dice state).level (descend dice state).monsters :=
  let plan := seeded dice.seed (() => generateLevel (state.level.depth + 1))
  placeMonstersOnFloor plan.level plan.level.start [] plan.monsters Trivial

theorem resolveOnFloor (dice: Dice) (state: State) (command: Command) (onFloor: OnFloor state.level state.monsters):
    OnFloor (resolve dice state command).level (resolve dice state command).monsters :=
  match phase: state.phase with
    | Playing =>
      match command with
        | Quit => onFloor
        | Wait => monstersTurnOnFloor dice { state | message = "You wait." } onFloor
        | Move direction => monstersTurnOnFloor dice (playerMoves dice state direction) (playerMovesOnFloor dice state direction onFloor)
        | Drink =>
          match none: state.potions == 0 with
            | True => onFloor
            | False => monstersTurnOnFloor dice (drink state) onFloor
        | Descend =>
          match stairs: isStairs state.level state.player with
            | True => descendOnFloor dice state onFloor
            | False => onFloor
    | Won => onFloor
    | Died => onFloor
    | GaveUp => onFloor

-- No monster stands in a wall after a turn, whatever the seed.
theorem stepOnFloor (seed: Nat) (state: State) (command: Command) (onFloor: OnFloor state.level state.monsters):
    OnFloor (seeded seed (() => step state command)).level (seeded seed (() => step state command)).monsters :=
  resolveOnFloor { seed = lcg seed / 65536 } state command onFloor
