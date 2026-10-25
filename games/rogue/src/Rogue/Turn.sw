-- One turn of the game: the player acts on a command, then each monster
-- acts. `step` is the whole turn; `resolve` is the same turn with its rolls
-- already made, which is what the proofs are about.

namespace Rogue
import Std (List, Text)

-- One turn. It draws one random number and makes all the turn's rolls from it.
def step (state: State) (command: Command): {Random} State :=
  let dice: Dice := { seed = next() }
  resolve dice state command

-- A turn with its rolls made. Once the game is over, nothing changes.
def resolve (dice: Dice) (state: State) (command: Command): State :=
  match state.phase with
    | Playing =>
      match command with
        | Quit => { state | phase = GaveUp, message = "You give up." }
        | Wait => monstersTurn dice { state | message = "You wait." }
        | Move direction => monstersTurn dice (playerMoves dice state direction)
    | _ => state

-- The player steps one cell, or attacks the monster standing there.
def playerMoves (dice: Dice) (state: State) (direction: Direction): State :=
  let target := state.player.toward direction
  match monsterAt target state.monsters with
    | Some monster => attack dice state monster
    | None => if isWall target then { state | message = "A wall blocks your way." } else enter state target

-- The player's blow.
def attack (dice: Dice) (state: State) (monster: Monster): State :=
  let damage := 2 + dice.upTo 0 (playerStrength - 2)
  let survivors := state.monsters
    |> .map (wound monster.position damage)
    |> .filter (other => other.hitPoints > 0)
  let message :=
    if damage < monster.hitPoints then "You hit the ${monster.kind.name} for ${damage}."
    else "You kill the ${monster.kind.name}!"
  { state | monsters = survivors, message }

-- The damage done to whichever monster stands on `target`.
def wound (target: Position) (damage: Nat) (monster: Monster): Monster :=
  if monster.position == target then { monster | hitPoints = monster.hitPoints - damage } else monster

-- The player walks onto a free cell, drinking any potion there.
def enter (state: State) (target: Position): State :=
  if state.potions.any (== target) then {
    state |
      player = target,
    potions = state.potions.filter (≠ target),
    hitPoints = healed state.hitPoints,
    message = "You drink a potion and feel better."
  }
  else { state | player = target, message = "" }

def healed (hitPoints: Nat): Nat :=
  if hitPoints + potionStrength ≤ maxHitPoints then hitPoints + potionStrength else maxHitPoints

-- After the player: escape by the stairs, or the monsters' turn.
def monstersTurn (dice: Dice) (state: State): State :=
  if isStairs state.player then { state | phase = Escaped, turn = state.turn + 1, message = "You find the stairs down and escape!" }
  else
    let outcome := actAll dice state.player 0 { moved = [], damage = 0, events = [] } state.monsters
    let hitPoints := state.hitPoints - outcome.damage
    let events := Text.join (Cons state.message outcome.events |> .filter (≠ "")) ' '
    let message := if hitPoints == 0 then "${events} You die..." else events
    let phase := if hitPoints == 0 then Died else Playing
    { state | monsters = outcome.moved, hitPoints, turn = state.turn + 1, message, phase }

-- The monsters' turn so far: those that have acted, the damage they have
-- done, and what happened.
type Outcome = { moved: List Monster, damage: Nat, events: List Text }

-- One more monster has acted: where it ended up, the damage it did, and
-- what happened.
def Outcome.add (outcome: Outcome) (monster: Monster) (damage: Nat) (events: List Text): Outcome :=
  { moved = outcome.moved ++ [monster], damage = outcome.damage + damage, events = outcome.events ++ events }

-- Each monster in turn attacks the player if it's next to them, and
-- otherwise moves. `index` numbers the monsters, to give each its own rolls.
def actAll (dice: Dice) (player: Position) (index: Nat) (outcome: Outcome): List Monster → Outcome
  | [] => outcome
  | Cons monster waiting =>
    if monster.position.isNextTo player then
      let damage := 1 + dice.upTo (3 * index + 1) (monster.kind.strength - 1)
      let event := "The ${monster.kind.name} hits you for ${damage}."
      actAll dice player (index + 1) (outcome.add monster damage [event]) waiting
    else
      let destination := pickFree (monsterChoices dice index player monster) player (outcome.moved ++ waiting) |> .getOrElse monster.position
      actAll dice player (index + 1) (outcome.add { monster | position = destination } 0 []) waiting

-- Where a monster would like to go, best first. One that can see the player
-- closes in, now and then stumbling; one that can't wanders, or stays put.
def monsterChoices (dice: Dice) (index: Nat) (player: Position) (monster: Monster): List Position :=
  let wanders := monster.position.distance player > sightRange ∨ dice.chance (3 * index + 2) 5
  if wanders then
    match dice.upTo (3 * index + 3) 7 with
      | 0 => [monster.position.toward North]
      | 1 => [monster.position.toward South]
      | 2 => [monster.position.toward West]
      | 3 => [monster.position.toward East]
      | _ => []
  else monster.position.closerTo player

-- The neighbouring cells that are closer to `target`, the direction with
-- further to go first.
def Position.closerTo (position: Position) (target: Position): List Position :=
  let vertical :=
    if target.row < position.row then [position.toward North]
    else if position.row < target.row then [position.toward South]
    else []
  let horizontal :=
    if target.column < position.column then [position.toward West]
    else if position.column < target.column then [position.toward East]
    else []
  if distanceBetween position.row target.row ≥ distanceBetween position.column target.column then vertical ++ horizontal
  else horizontal ++ vertical

-- The first cell that isn't a wall, the player, or another monster's.
def pickFree (choices: List Position) (player: Position) (others: List Monster): Option Position :=
  match choices with
    | [] => None
    | Cons choice rest =>
      if isWall choice ∨ choice == player ∨ (monsterAt choice others).isSome then pickFree rest player others
      else Some choice
