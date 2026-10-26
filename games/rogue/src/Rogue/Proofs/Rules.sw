-- The rules of a turn, proved for every seed:
--
-- - once the game is won, lost or given up, nothing changes
--   (`resolveFinished`), and quitting gives up (`resolveQuit`);
-- - moving onto a cell with no monster and no wall puts the player there
--   (`resolveMoves`);
-- - only monsters next to the player hurt them, and by at most the sum of
--   those monsters' strengths (`monstersTurnHurt`, `monstersTurnHarmless`);
-- - hit points only go up by drinking a potion, and then by at most
--   `potionStrength` (`resolveNoHeal`, `resolveDrinkHeals`).

namespace Rogue.Proofs
import Rogue (..)
import Std (Eq, List, Nat, Option, Void)

theorem resolveFinished (dice: Dice) (state: State) (command: Command) (over: state.phase ≠ Playing): resolve dice state command = state :=
  match phase: state.phase with
    | Playing => Void.exfalso (over rfl)
    | Won => rfl
    | Died => rfl
    | GaveUp => rfl

theorem resolveQuit (dice: Dice) (state: State) (playing: state.phase = Playing): (resolve dice state Quit).phase = GaveUp :=
  rewrite playing in rfl

-- The most the monsters next to `player` could do in one turn: each one's
-- strength.
def threat (player: Position): List Monster → Nat
  | [] => 0
  | Cons monster rest => (if monster.position.isNextTo player then monster.kind.strength else 0) + threat player rest

theorem upToAtMost (dice: Dice) (index: Nat) (most: Nat): dice.upTo index most ≤ most :=
  omega [Nat.modLt (lcg (lcg (dice.seed + index * 7919)) / 65536) (most + 1)]

theorem strengthPositive: (kind: Kind) → 1 ≤ kind.strength
  | Goblin => rfl
  | Orc => rfl
  | Troll => rfl

theorem blowAtMost (dice: Dice) (index: Nat) (kind: Kind): 1 + dice.upTo index (kind.strength - 1) ≤ kind.strength :=
  omega [upToAtMost dice index (kind.strength - 1), strengthPositive kind]

theorem actAllDamage (dice: Dice) (level: Level) (player: Position):
    (index: Nat) → (outcome: Outcome) → (waiting: List Monster) →
    (actAll dice level player index outcome waiting).damage ≤ outcome.damage + threat player waiting
  | index, outcome, [] => omega
  | index, outcome, Cons monster waiting =>
    match next: monster.position.isNextTo player with
      | True =>
        let rest := actAllDamage dice level player (index + 1) (outcome.add monster (1 + dice.upTo (3 * index + 1) (monster.kind.strength - 1)) ["The ${monster.kind.name} hits you for ${1 + dice.upTo (3 * index + 1) (monster.kind.strength - 1)}."]) waiting
        omega [rest, blowAtMost dice (3 * index + 1) monster.kind]
      | False =>
        let destination := pickFree level (monsterChoices dice index player monster) player (outcome.moved ++ waiting) |> .getOrElse monster.position
        let rest := actAllDamage dice level player (index + 1) (outcome.add { monster | position = destination } 0 []) waiting
        omega [rest]

theorem monstersTurnHurt (dice: Dice) (state: State):
    state.hitPoints ≤ (monstersTurn dice state).hitPoints + threat state.player state.monsters :=
  match phase: state.phase with
    | Playing => omega [actAllDamage dice state.level state.player 0 { moved = [], damage = 0, events = [] } state.monsters]
    | Won => omega
    | Died => omega
    | GaveUp => omega

theorem threatNone (player: Position): (monsters: List Monster) → List.All (monster => monster.position.isNextTo player = False) monsters → threat player monsters = 0
  | [], none => rfl
  | Cons monster rest, Both far others => rewrite far, threatNone player rest others in rfl

theorem monstersTurnNoHeal (dice: Dice) (state: State): (monstersTurn dice state).hitPoints ≤ state.hitPoints :=
  match phase: state.phase with
    | Playing => omega
    | Won => omega
    | Died => omega
    | GaveUp => omega

-- With no monster next to the player, the monsters' turn costs nothing.
theorem monstersTurnHarmless (dice: Dice) (state: State) (none: List.All (monster => monster.position.isNextTo state.player = False) state.monsters):
    (monstersTurn dice state).hitPoints = state.hitPoints :=
  omega [monstersTurnHurt dice state, monstersTurnNoHeal dice state, threatNone state.player state.monsters none]

theorem descendHitPoints (dice: Dice) (state: State): (descend dice state).hitPoints = state.hitPoints :=
  rfl

theorem playerMovesHitPoints (dice: Dice) (state: State) (direction: Direction): (playerMoves dice state direction).hitPoints = state.hitPoints :=
  match found: monsterAt (state.player.toward direction) state.monsters with
    | Some monster => rfl
    | None =>
      match wall: isWall state.level (state.player.toward direction) with
        | True => rfl
        | False => enterHitPoints state (state.player.toward direction)

-- Hit points only go up by drinking a potion.
theorem resolveNoHeal (dice: Dice) (state: State) (command: Command) (notDrink: command ≠ Drink):
    (resolve dice state command).hitPoints ≤ state.hitPoints :=
  match phase: state.phase with
    | Playing =>
      match command with
        | Quit => omega
        | Wait => monstersTurnNoHeal dice { state | message = "You wait." }
        | Move direction => omega [monstersTurnNoHeal dice (playerMoves dice state direction), playerMovesHitPoints dice state direction]
        | Drink => Void.exfalso (notDrink rfl)
        | Descend =>
          match stairs: isStairs state.level state.player with
            | True => omega [descendHitPoints dice state]
            | False => omega
    | Won => omega
    | Died => omega
    | GaveUp => omega

theorem healedAtMostPotion (hitPoints: Nat): healed hitPoints ≤ hitPoints + potionStrength :=
  match fits: Nat.leq (hitPoints + potionStrength) maxHitPoints with
    | True => omega
    | False => omega

-- And a potion heals at most `potionStrength`.
theorem resolveDrinkHeals (dice: Dice) (state: State): (resolve dice state Drink).hitPoints ≤ state.hitPoints + potionStrength :=
  match phase: state.phase with
    | Playing =>
      match none: state.potions == 0 with
        | True => omega
        | False => omega [monstersTurnNoHeal dice (drink state), healedAtMostPotion state.hitPoints]
    | Won => omega
    | Died => omega
    | GaveUp => omega
-- Moving onto a cell with no monster and no wall puts the player there.
theorem resolveMoves (dice: Dice) (state: State) (direction: Direction) (playing: state.phase = Playing)
    (vacant: monsterAt (state.player.toward direction) state.monsters = None) (open: isWall state.level (state.player.toward direction) = False):
    (resolve dice state (Move direction)).player = state.player.toward direction :=
  rewrite playing, monstersTurnPlayer dice (playerMoves dice state direction) in
    rewrite vacant, open in enterPlayer state (state.player.toward direction)
