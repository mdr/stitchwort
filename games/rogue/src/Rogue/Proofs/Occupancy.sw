-- No monster stands on the player's cell after a turn (`stepClear`). The
-- player only steps where no monster is (or attacks it instead); a blow
-- changes monsters without moving them; each monster either stays put (and
-- it wasn't on the player's cell) or moves to a cell `pickFree` has checked
-- isn't the player's; and a new level's monsters are placed by `pickFree`
-- too (Level.sw).

namespace Rogue.Proofs
import Rogue (..)
import Std (Decidable, Eq, List, Option, Void, Bool)

-- No monster stands on `position`.
def Clear (position: Position) (monsters: List Monster): Prop := monsterAt position monsters = None

theorem someNotNone (monster: Monster) (found: Some monster = None): Void := Option.noneNotSome monster (Eq.sym found)

-- The first monster of a clear list isn't on the cell, and the rest are clear.
theorem clearHead (position: Position) (monster: Monster) (others: List Monster) (clear: Clear position (Cons monster others)):
    (monster.position == position) = False :=
  match same: monster.position == position with
    | True => Void.exfalso (someNotNone monster clear)
    | False => rfl

theorem clearTail (position: Position) (monster: Monster) (others: List Monster) (clear: Clear position (Cons monster others)):
    Clear position others :=
  match same: monster.position == position with
    | True => Void.exfalso (someNotNone monster clear)
    | False => clear

theorem clearSnoc (position: Position) (monster: Monster) (away: (monster.position == position) = False):
    (monsters: List Monster) → Clear position monsters → Clear position (monsters ++ [monster])
  | [], clear => rewrite away
  | Cons first rest, clear =>
    match same: first.position == position with
      | True => Void.exfalso (someNotNone first clear)
      | False => clearSnoc position monster away rest clear

-- A monster never chooses the player's cell.
theorem pickFreeAway (level: Level) (player: Position) (others: List Monster):
    (choices: List Position) → (destination: Position) → pickFree level choices player others = Some destination → (destination == player) = False
  | [], destination, picked => Void.exfalso (Option.noneNotSome destination picked)
  | Cons choice rest, destination, picked =>
    match wall: isWall level choice with
      | True => pickFreeAway level player others rest destination picked
      | False =>
        match same: choice == player with
          | True => pickFreeAway level player others rest destination picked
          | False =>
            match taken: (monsterAt choice others).isSome with
              | True => pickFreeAway level player others rest destination picked
              | False => rewrite <- Option.someInjective choice destination picked in same

-- Changing monsters without moving them keeps them off the cell.
theorem clearMap (position: Position) (change: Monster → Monster) (stays: (monster: Monster) → (change monster).position = monster.position):
    (monsters: List Monster) → Clear position monsters → Clear position (monsters.map change)
  | [], clear => rfl
  | Cons first rest, clear =>
    rewrite stays first, clearHead position first rest clear in clearMap position change stays rest (clearTail position first rest clear)

-- Dropping monsters keeps the rest off the cell.
theorem clearFilter (position: Position) (keep: Monster → Bool):
    (monsters: List Monster) → Clear position monsters → Clear position (monsters.filter keep)
  | [], clear => rfl
  | Cons first rest, clear =>
    match kept: keep first with
      | True => rewrite clearHead position first rest clear in clearFilter position keep rest (clearTail position first rest clear)
      | False => clearFilter position keep rest (clearTail position first rest clear)

theorem woundStays (target: Position) (damage: Nat) (monster: Monster): (wound target damage monster).position = monster.position :=
  match hit: monster.position == target with
    | True => rfl
    | False => rfl

-- The monsters' turn keeps them off the player's cell: those that attack
-- stay where they are, and those that move pick a free cell, or stay.
theorem actAllClear (dice: Dice) (level: Level) (player: Position):
    (index: Nat) → (outcome: Outcome) → (waiting: List Monster) →
    Clear player outcome.moved → Clear player waiting → Clear player (actAll dice level player index outcome waiting).moved
  | index, outcome, [], moved, rest => moved
  | index, outcome, Cons monster waiting, moved, clear =>
    let away := clearHead player monster waiting clear
    let rest := clearTail player monster waiting clear
    match next: monster.position.isNextTo player with
      | True => actAllClear dice level player (index + 1) (outcome.add monster _ _) waiting (clearSnoc player monster away outcome.moved moved) rest
      | False =>
        match picked: pickFree level (monsterChoices dice index player monster) player (outcome.moved ++ waiting) with
          | Some destination =>
            let fresh := pickFreeAway level player (outcome.moved ++ waiting) (monsterChoices dice index player monster) destination picked
            actAllClear dice level player (index + 1) (outcome.add { monster | position = destination } 0 []) waiting (clearSnoc player { monster | position = destination } fresh outcome.moved moved) rest
          | None => actAllClear dice level player (index + 1) (outcome.add { monster | position = monster.position } 0 []) waiting (clearSnoc player { monster | position = monster.position } away outcome.moved moved) rest

theorem monstersTurnClear (dice: Dice) (state: State) (clear: Clear state.player state.monsters):
    let after := monstersTurn dice state
    Clear after.player after.monsters :=
  match phase: state.phase with
    | Playing => actAllClear dice state.level state.player 0 { moved = [], damage = 0, events = [] } state.monsters rfl clear
    | Won => clear
    | Died => clear
    | GaveUp => clear

theorem playerMovesClear (dice: Dice) (state: State) (direction: Direction) (clear: Clear state.player state.monsters):
    let after := playerMoves dice state direction
    Clear after.player after.monsters :=
  match found: monsterAt (state.player.toward direction) state.monsters with
    | Some monster =>
      let damage := 2 + dice.upTo 0 (state.strength - 2)
      let wounded := state.monsters.map (wound monster.position damage)
      clearFilter state.player (other => other.hitPoints > 0) wounded
        (clearMap state.player (wound monster.position damage) (woundStays monster.position damage) state.monsters clear)
    | None =>
      match wall: isWall state.level (state.player.toward direction) with
        | True => clear
        | False =>
          let target := state.player.toward direction
          rewrite enterPlayer state target, enterMonsters state target in found

theorem descendClear (dice: Dice) (state: State) (clear: Clear state.player state.monsters):
    let after := descend dice state
    Clear after.player after.monsters :=
  let plan := seeded dice.seed (() => generateLevel (state.level.depth + 1))
  placeMonstersClear plan.level plan.level.start [] plan.monsters rfl

theorem resolveClear (dice: Dice) (state: State) (command: Command) (clear: Clear state.player state.monsters):
    let after := resolve dice state command
    Clear after.player after.monsters :=
  match phase: state.phase with
    | Playing =>
      match command with
        | Quit => clear
        | Wait => monstersTurnClear dice { state | message = "You wait." } clear
        | Move direction => monstersTurnClear dice (playerMoves dice state direction) (playerMovesClear dice state direction clear)
        | Drink =>
          match none: state.potions == 0 with
            | True => clear
            | False => monstersTurnClear dice (drink state) clear
        | Descend =>
          match stairs: isStairs state.level state.player with
            | True => descendClear dice state clear
            | False => clear
    | Won => clear
    | Died => clear
    | GaveUp => clear

-- No monster stands on the player's cell after a turn, whatever the seed.
theorem stepClear (seed: Nat) (state: State) (command: Command) (clear: Clear state.player state.monsters):
    let after := seeded seed (() => step state command)
    Clear after.player after.monsters :=
  resolveClear { seed = lcg seed / 65536 } state command clear
