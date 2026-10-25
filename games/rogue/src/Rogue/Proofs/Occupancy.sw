-- No monster stands on the player's cell after a turn (`stepClear`). The
-- player only steps where no monster is (or attacks it instead); a blow
-- changes monsters without moving them; and each monster either stays put
-- (and it wasn't on the player's cell) or moves to a cell `pickFree` has
-- checked isn't the player's.

namespace Rogue.Proofs
import Rogue (..)
import Std (Eq, List, Option, Void, Bool)

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

theorem clearCons (position: Position) (monster: Monster) (others: List Monster) (away: (monster.position == position) = False) (clear: Clear position others):
    Clear position (Cons monster others) :=
  rewrite away in clear

theorem clearSnoc (position: Position) (monster: Monster) (away: (monster.position == position) = False):
    (monsters: List Monster) → Clear position monsters → Clear position (monsters ++ [monster])
  | [], clear => rewrite away
  | Cons first rest, clear =>
    match same: first.position == position with
      | True => Void.exfalso (someNotNone first clear)
      | False => clearSnoc position monster away rest clear

-- A monster never chooses the player's cell.
theorem pickFreeAway (player: Position) (others: List Monster):
    (choices: List Position) → (destination: Position) → pickFree choices player others = Some destination → (destination == player) = False
  | [], destination, picked => Void.exfalso (Option.noneNotSome destination picked)
  | Cons choice rest, destination, picked =>
    match wall: isWall choice with
      | True => pickFreeAway player others rest destination picked
      | False =>
        match same: choice == player with
          | True => pickFreeAway player others rest destination picked
          | False =>
            match taken: (monsterAt choice others).isSome with
              | True => pickFreeAway player others rest destination picked
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
theorem actAllClear (dice: Dice) (player: Position):
    (index: Nat) → (outcome: Outcome) → (waiting: List Monster) →
    Clear player outcome.moved → Clear player waiting → Clear player (actAll dice player index outcome waiting).moved
  | index, outcome, [], moved, rest => moved
  | index, outcome, Cons monster waiting, moved, clear =>
    let away := clearHead player monster waiting clear
    let rest := clearTail player monster waiting clear
    match next: monster.position.isNextTo player with
      | True => actAllClear dice player (index + 1) (outcome.add monster _ _) waiting (clearSnoc player monster away outcome.moved moved) rest
      | False =>
        match picked: pickFree (monsterChoices dice index player monster) player (outcome.moved ++ waiting) with
          | Some destination =>
            let fresh := pickFreeAway player (outcome.moved ++ waiting) (monsterChoices dice index player monster) destination picked
            actAllClear dice player (index + 1) (outcome.add { monster | position = destination } 0 []) waiting (clearSnoc player { monster | position = destination } fresh outcome.moved moved) rest
          | None => actAllClear dice player (index + 1) (outcome.add { monster | position = monster.position } 0 []) waiting (clearSnoc player { monster | position = monster.position } away outcome.moved moved) rest

theorem monstersTurnClear (dice: Dice) (state: State) (clear: Clear state.player state.monsters):
    Clear (monstersTurn dice state).player (monstersTurn dice state).monsters :=
  match stairs: isStairs state.player with
    | True => clear
    | False => actAllClear dice state.player 0 { moved = [], damage = 0, events = [] } state.monsters rfl clear

theorem enterClear (state: State) (target: Position) (free: Clear target state.monsters):
    Clear (enter state target).player (enter state target).monsters :=
  match potion: state.potions.any (== target) with
    | True => free
    | False => free

theorem playerMovesClear (dice: Dice) (state: State) (direction: Direction) (clear: Clear state.player state.monsters):
    Clear (playerMoves dice state direction).player (playerMoves dice state direction).monsters :=
  match found: monsterAt (state.player.toward direction) state.monsters with
    | Some monster =>
      let damage := 2 + dice.upTo 0 (playerStrength - 2)
      let wounded := state.monsters.map (wound monster.position damage)
      clearFilter state.player (other => other.hitPoints > 0) wounded
        (clearMap state.player (wound monster.position damage) (woundStays monster.position damage) state.monsters clear)
    | None =>
      match wall: isWall (state.player.toward direction) with
        | True => clear
        | False => enterClear state (state.player.toward direction) found

theorem resolveClear (dice: Dice) (state: State) (command: Command) (clear: Clear state.player state.monsters):
    Clear (resolve dice state command).player (resolve dice state command).monsters :=
  match phase: state.phase with
    | Playing =>
      match command with
        | Quit => clear
        | Wait => monstersTurnClear dice { state | message = "You wait." } clear
        | Move direction => monstersTurnClear dice (playerMoves dice state direction) (playerMovesClear dice state direction clear)
    | Escaped => clear
    | Died => clear
    | GaveUp => clear

-- No monster stands on the player's cell after a turn, whatever the seed.
theorem stepClear (seed: Nat) (state: State) (command: Command) (clear: Clear state.player state.monsters):
    Clear (seeded seed (() => step state command)).player (seeded seed (() => step state command)).monsters :=
  resolveClear { seed = lcg seed / 65536 } state command clear
