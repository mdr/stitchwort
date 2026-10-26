-- No two monsters share a cell after a turn (`stepApart`): their positions
-- are a list with no repeats (`List.Distinct`). A blow changes monsters
-- without moving them and only removes some; each monster either stays put
-- or moves to a cell `pickFree` has checked no other monster stands on; and
-- a new level's monsters are placed by `pickFree` too.

namespace Rogue.Proofs
import Rogue (..)
import Std (Bool, DecEq, Decidable, Eq, List, Nat, Option, Void)

-- Where the monsters stand.
def positions (monsters: List Monster): List Position := monsters.map (monster => monster.position)

-- No two monsters stand on one cell.
def Apart (monsters: List Monster): Prop := List.Distinct (positions monsters)

theorem memAppendLeft (x: a) (ys: List a): (xs: List a) → List.Mem x xs → List.Mem x (xs ++ ys)
  | [], inside => Void.exfalso inside
  | Cons first rest, Inl here => Inl here
  | Cons first rest, Inr later => Inr (memAppendLeft x ys rest later)

theorem memAppendRight (x: a) (ys: List a): (xs: List a) → List.Mem x ys → List.Mem x (xs ++ ys)
  | [], inside => inside
  | Cons first rest, inside => Inr (memAppendRight x ys rest inside)

-- One element of a list with no repeats replaced by one not among the others.
theorem distinctSwap (x: a) (y: a) (after: List a): (before: List a) →
    List.Distinct (before ++ Cons x after) → Not (List.Mem y (before ++ after)) → List.Distinct (before ++ Cons y after)
  | [], Both notMem rest, fresh => Both fresh rest
  | Cons first others, Both notMem rest, fresh =>
    let away: Not (List.Mem first (others ++ Cons y after)) := inside =>
      match List.memAppend first others (Cons y after) inside with
        | Inl early => notMem (memAppendLeft first (Cons x after) others early)
        | Inr (Inl same) => fresh (Inl (Eq.sym same))
        | Inr (Inr late) => notMem (memAppendRight first (Cons x after) others (Inr late))
    Both away (distinctSwap x y after others rest (inside => fresh (Inr inside)))

theorem distinctSnoc (y: a): (xs: List a) → List.Distinct xs → Not (List.Mem y xs) → List.Distinct (xs ++ [y])
  | [], none, fresh => Both (inside => inside) Trivial
  | Cons first rest, Both notMem others, fresh =>
    let away: Not (List.Mem first (rest ++ [y])) := inside =>
      match List.memAppend first rest [y] inside with
        | Inl early => notMem early
        | Inr (Inl same) => fresh (Inl (Eq.sym same))
        | Inr (Inr none) => none
    Both away (distinctSnoc y rest others (inside => fresh (Inr inside)))

-- A cell with no monster on it isn't among their positions.
theorem vacantNotMem (position: Position): (monsters: List Monster) → monsterAt position monsters = None → Not (List.Mem position (positions monsters))
  | [], vacant, inside => inside
  | Cons monster others, vacant, inside =>
    match same: monster.position == position with
      | True => Option.noneNotSome monster (Eq.sym vacant)
      | False =>
        match inside with
          | Inl here => DecEq.soundFalse monster.position position same here
          | Inr later => vacantNotMem position others vacant later

-- A monster never chooses another monster's cell.
theorem pickFreeVacant (level: Level) (player: Position) (others: List Monster):
    (choices: List Position) → (destination: Position) → pickFree level choices player others = Some destination → monsterAt destination others = None
  | [], destination, picked => Void.exfalso (Option.noneNotSome destination picked)
  | Cons choice rest, destination, picked =>
    match wall: isWall level choice with
      | True => pickFreeVacant level player others rest destination picked
      | False =>
        match same: choice == player with
          | True => pickFreeVacant level player others rest destination picked
          | False =>
            match found: monsterAt choice others with
              | Some monster => pickFreeVacant level player others rest destination picked
              | None => rewrite <- Option.someInjective choice destination picked in found

theorem positionsAppend (xs: List Monster) (ys: List Monster): positions (xs ++ ys) = positions xs ++ positions ys :=
  List.mapAppend xs ys (monster => monster.position)

-- A monster that stays where it was keeps them apart...
theorem apartStay (moved: List Monster) (monster: Monster) (stayed: Monster) (same: stayed.position = monster.position) (waiting: List Monster)
    (apart: Apart (moved ++ Cons monster waiting)): Apart ((moved ++ [stayed]) ++ waiting) :=
  rewrite List.appendAssoc moved [stayed] waiting, positionsAppend moved (Cons stayed waiting), same in
    rewrite <- positionsAppend moved (Cons monster waiting) in apart

-- ...and so does one that moves to a cell no other monster stands on.
theorem apartMove (moved: List Monster) (monster: Monster) (destination: Position) (waiting: List Monster)
    (apart: Apart (moved ++ Cons monster waiting)) (vacant: monsterAt destination (moved ++ waiting) = None):
    Apart ((moved ++ [{ monster | position = destination }]) ++ waiting) :=
  let fresh := vacantNotMem destination (moved ++ waiting) vacant
  rewrite List.appendAssoc moved [{ monster | position = destination }] waiting, positionsAppend moved (Cons ({ monster | position = destination }) waiting) in
    distinctSwap monster.position destination (positions waiting) (positions moved)
      (rewrite <- positionsAppend moved (Cons monster waiting) in apart)
      (rewrite <- positionsAppend moved waiting in fresh)

theorem actAllApart (dice: Dice) (level: Level) (player: Position):
    (index: Nat) → (outcome: Outcome) → (waiting: List Monster) →
    Apart (outcome.moved ++ waiting) → Apart (actAll dice level player index outcome waiting).moved
  | index, outcome, [], apart => rewrite <- List.appendNil outcome.moved in apart
  | index, outcome, Cons monster waiting, apart =>
    match next: monster.position.isNextTo player with
      | True => actAllApart dice level player (index + 1) (outcome.add monster _ _) waiting (apartStay outcome.moved monster monster rfl waiting apart)
      | False =>
        match picked: pickFree level (monsterChoices dice index player monster) player (outcome.moved ++ waiting) with
          | Some destination =>
            let vacant := pickFreeVacant level player (outcome.moved ++ waiting) (monsterChoices dice index player monster) destination picked
            actAllApart dice level player (index + 1) (outcome.add { monster | position = destination } 0 []) waiting (apartMove outcome.moved monster destination waiting apart vacant)
          | None => actAllApart dice level player (index + 1) (outcome.add { monster | position = monster.position } 0 []) waiting (apartStay outcome.moved monster { monster | position = monster.position } rfl waiting apart)

theorem monstersTurnApart (dice: Dice) (state: State) (apart: Apart state.monsters): Apart (monstersTurn dice state).monsters :=
  match phase: state.phase with
    | Playing => actAllApart dice state.level state.player 0 { moved = [], damage = 0, events = [] } state.monsters apart
    | Won => apart
    | Died => apart
    | GaveUp => apart

theorem positionsWound (target: Position) (damage: Nat): (monsters: List Monster) → positions (monsters.map (wound target damage)) = positions monsters
  | [] => rfl
  | Cons monster others => rewrite woundStays target damage monster, positionsWound target damage others in rfl

theorem playerMovesApart (dice: Dice) (state: State) (direction: Direction) (apart: Apart state.monsters):
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

-- A new level's monsters are placed one to a cell.
theorem placeMonstersApart (level: Level) (start: Position):
    (placed: List Monster) → (planned: List Monster) → Apart placed → Apart (placeMonsters level start placed planned)
  | placed, [], apart => apart
  | placed, Cons monster rest, apart =>
    match picked: pickFree level [monster.position] start placed with
      | Some position =>
        let fresh := vacantNotMem position placed (pickFreeVacant level start placed [monster.position] position picked)
        let joined: Apart (placed ++ [{ monster | position }]) := rewrite positionsAppend placed [{ monster | position }] in distinctSnoc position (positions placed) apart fresh
        placeMonstersApart level start (placed ++ [{ monster | position }]) rest joined
      | None => placeMonstersApart level start placed rest apart

theorem descendApart (dice: Dice) (state: State) (apart: Apart state.monsters): Apart (descend dice state).monsters :=
  let plan := seeded dice.seed (() => generateLevel (state.level.depth + 1))
  placeMonstersApart plan.level plan.level.start [] plan.monsters Trivial

theorem resolveApart (dice: Dice) (state: State) (command: Command) (apart: Apart state.monsters): Apart (resolve dice state command).monsters :=
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

-- No two monsters share a cell after a turn, whatever the seed.
theorem stepApart (seed: Nat) (state: State) (command: Command) (apart: Apart state.monsters):
    Apart (seeded seed (() => step state command)).monsters :=
  resolveApart { seed = lcg seed / 65536 } state command apart

-- With the monsters apart, the monster found on each monster's cell is
-- that monster.
theorem monsterAtOwnCell (found: Monster): (monsters: List Monster) → Apart monsters → List.Mem found monsters → monsterAt found.position monsters = Some found
  | [], apart, inside => Void.exfalso inside
  | Cons monster others, Both notMem rest, Inl same => rewrite same, DecEq.refl found.position in rfl
  | Cons monster others, Both notMem rest, Inr later =>
    let elsewhere: Not (monster.position = found.position) := same =>
      notMem (rewrite same in List.memMap others found later (monster => monster.position))
    rewrite Decidable.toBoolOfNot (DecEq.decide monster.position found.position) elsewhere in monsterAtOwnCell found others rest later
