--| No two monsters share a cell after a turn (`stepApart`): their positions
--| are a list with no repeats (`List.Distinct`). A blow changes monsters
--| without moving them and only removes some; each monster either stays put
--| or moves to a cell `pickFree` has checked no other monster stands on; and
--| a new level's monsters are placed by `pickFree` too.

namespace Rogue.Proofs
import Rogue (..)
import Std (Bool, DecEq, Decidable, Eq, List, Nat, Option, Void)

--| Where the monsters stand.
def positions (monsters: List Monster): List Position := monsters.map (monster => monster.position)

--| No two monsters stand on one cell.
def Apart (monsters: List Monster): Prop := List.Distinct (positions monsters)

theorem memAppendLeft ∀ (x: a) (ys: List a) (xs: List a) (inside: List.Mem x xs): List.Mem x (xs ++ ys) :=
  match xs, inside with
    | [], inside => Void.exfalso inside
    | [first, ..rest], Inl here => Inl here
    | [first, ..rest], Inr later => Inr (memAppendLeft x ys rest later)

theorem memAppendRight ∀ (x: a) (ys: List a) (xs: List a) (inside: List.Mem x ys): List.Mem x (xs ++ ys) :=
  match xs with
    | [] => inside
    | [first, ..rest] => Inr (memAppendRight x ys rest inside)

--| A cell with no monster on it isn't among their positions.
theorem vacantNotMem ∀ (position: Position) (monsters: List Monster) (vacant: monsterAt position monsters = None):
    ¬(List.Mem position (positions monsters)) := match monsters with
      | [] => inside => inside
      | [monster, ..others] => inside =>
        match same: monster.position == position with
          | False =>
            match inside with
              | Inl here => same.read here
              | Inr later => vacantNotMem position others vacant later

--| A monster never chooses another monster's cell.
theorem pickFreeVacant ∀ (level: Level) (player: Position) (others: List Monster)
    (choices: List Position) (destination: Position) (picked: pickFree level choices player others = Some destination): monsterAt destination others = None :=
  match choices with
    | [choice, ..rest] =>
      match wall: isWall level choice with
        | True => pickFreeVacant level player others rest destination picked
        | False =>
          match same: choice == player with
            | True => pickFreeVacant level player others rest destination picked
            | False =>
              match found: monsterAt choice others with
                | Some monster => pickFreeVacant level player others rest destination picked
                | None => rewrite <- Option.someInjective picked in found

theorem positionsAppend ∀ (xs: List Monster) (ys: List Monster): positions (xs ++ ys) = positions xs ++ positions ys :=
  List.mapAppend xs ys (monster => monster.position)

--| A monster that stays where it was keeps them apart...
theorem apartStay ∀ (moved: List Monster) (monster: Monster) (stayed: Monster) (same: stayed.position = monster.position) (waiting: List Monster)
    (apart: Apart (moved ++ [monster, ..waiting])): Apart ((moved ++ [stayed]) ++ waiting) :=
  rewrite List.appendAssoc moved [stayed] waiting, positionsAppend moved [stayed, ..waiting], same in
    rewrite <- positionsAppend moved [monster, ..waiting] in apart

--| ...and so does one that moves to a cell no other monster stands on.
theorem apartMove ∀ (moved: List Monster) (monster: Monster) (destination: Position) (waiting: List Monster)
    (apart: Apart (moved ++ [monster, ..waiting])) (vacant: monsterAt destination (moved ++ waiting) = None):
    Apart ((moved ++ [{ monster | position = destination }]) ++ waiting) :=
  let fresh := vacantNotMem destination (moved ++ waiting) vacant
  rewrite List.appendAssoc moved [{ monster | position = destination }] waiting, positionsAppend moved [{ monster | position = destination }, ..waiting] in
    List.distinctSwapMiddle monster.position destination (positions waiting) (positions moved)
      (rewrite <- positionsAppend moved [monster, ..waiting] in apart)
      (rewrite <- positionsAppend moved waiting in fresh)

theorem actAllApart ∀ (dice: Dice) (level: Level) (player: Position)
    (index: Nat) (outcome: Outcome) (waiting: List Monster)
    (apart: Apart (outcome.moved ++ waiting)): Apart (actAll dice level player index outcome waiting).moved :=
  match waiting with
    | [] => rewrite <- List.appendNil outcome.moved in apart
    | [monster, ..waiting] =>
      match next: monster.position.isNextTo player with
        | True => actAllApart dice level player (index + 1) _ waiting (apartStay outcome.moved monster monster rfl waiting apart)
        | False =>
          match picked: pickFree level (monsterChoices dice index player monster) player (outcome.moved ++ waiting) with
            | Some destination =>
              let vacant := pickFreeVacant level player (outcome.moved ++ waiting) (monsterChoices dice index player monster) destination picked
              actAllApart dice level player (index + 1) _ waiting (apartMove outcome.moved monster destination waiting apart vacant)
            | None => actAllApart dice level player (index + 1) _ waiting (apartStay outcome.moved monster { monster | position = monster.position } rfl waiting apart)

theorem monstersTurnApart ∀ (dice: Dice) (state: State) (apart: Apart state.monsters): Apart (monstersTurn dice state).monsters :=
  match phase: state.phase with
    | Playing => actAllApart dice state.level state.player 0 { moved = [], damage = 0, events = [] } state.monsters apart
    | Won => apart
    | Died => apart
    | GaveUp => apart

theorem positionsWound ∀ (target: Position) (damage: Nat) (monsters: List Monster): positions (monsters.map (wound target damage)) = positions monsters :=
  match monsters with
    | [] => rfl
    | [monster, ..others] => rewrite woundStays target damage monster, positionsWound target damage others in rfl

theorem playerMovesApart ∀ (dice: Dice) (state: State) (direction: Direction) (apart: Apart state.monsters):
    Apart (playerMoves dice state direction).monsters :=
  match found: monsterAt (state.player.toward direction) state.monsters with
    | Some monster =>
      let damage := 2 + dice.upTo 0 (state.strength - 2)
      let wounded := state.monsters.map (wound monster.position damage)
      List.distinctMapFilter wounded (monster => monster.position) (other => other.hitPoints > 0)
        (rewrite positionsWound monster.position damage state.monsters in apart)
    | None =>
      match wall: isWall state.level (state.player.toward direction) with
        | True => apart
        | False => rewrite enterMonsters state (state.player.toward direction) in apart

--| A new level's monsters are placed one to a cell.
theorem placeMonstersApart ∀ (level: Level) (start: Position)
    (placed planned: List Monster) (apart: Apart placed): Apart (placeMonsters level start placed planned) :=
  match planned with
    | [] => apart
    | [monster, ..rest] =>
      match picked: pickFree level [monster.position] start placed with
        | Some position =>
          let fresh := vacantNotMem position placed (pickFreeVacant level start placed [monster.position] position picked)
          let joined: Apart (placed ++ [{ monster | position }]) := rewrite positionsAppend placed [{ monster | position }] in List.distinctSnoc (positions placed) position fresh apart
          placeMonstersApart level start (placed ++ [{ monster | position }]) rest joined
        | None => placeMonstersApart level start placed rest apart

theorem descendApart ∀ (dice: Dice) (state: State) (apart: Apart state.monsters): Apart (descend dice state).monsters :=
  let plan := Random.withSeed dice.seed (() => generateLevel (state.level.depth + 1))
  placeMonstersApart plan.level plan.level.start [] plan.monsters Trivial

theorem resolveApart ∀ (dice: Dice) (state: State) (command: Command) (apart: Apart state.monsters): Apart (resolve dice state command).monsters :=
  match phase: state.phase with
    | Playing =>
      match command with
        | Quit => apart
        | Wait => monstersTurnApart dice { state | message = "You wait." } apart
        | Move direction => monstersTurnApart dice (playerMoves dice state direction) (playerMovesApart dice state direction apart)
        | Drink =>
          match none: state.potions == 0 with
            | True => apart
            | False => monstersTurnApart dice (drink state) apart
        | Descend =>
          match stairs: isStairs state.level state.player with
            | True => descendApart dice state apart
            | False => apart
    | Won => apart
    | Died => apart
    | GaveUp => apart

--| No two monsters share a cell after a turn, whatever the seed.
theorem stepApart ∀ (seed: Nat) (state: State) (command: Command) (apart: Apart state.monsters):
    Apart (Random.withSeed seed (() => step state command)).monsters :=
  resolveApart { seed = lcg seed / 65536 } state command apart

--| With the monsters apart, the monster found on each monster's cell is
--| that monster.
theorem monsterAtOwnCell ∀ (found: Monster) (monsters: List Monster) (apart: Apart monsters) (inside: List.Mem found monsters): monsterAt found.position monsters = Some found :=
  match monsters, apart, inside with
    | [], apart, inside => Void.exfalso inside
    | [monster, ..others], Both notMem rest, Inl same => rewrite same, DecEq.refl found.position in rfl
    | [monster, ..others], Both notMem rest, Inr later =>
      let elsewhere: monster.position ≠ found.position := same =>
        notMem (rewrite same in List.memMap others found later (monster => monster.position))
      rewrite Decidable.toBoolOfNot (DecEq.decide monster.position found.position) elsewhere in monsterAtOwnCell found others rest later
