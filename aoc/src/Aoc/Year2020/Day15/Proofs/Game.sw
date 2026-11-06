--| The game follows the spec turn by turn: after each turn, its last number
--| is the spec's latest and its map gives, for every number, the turn the
--| spec last spoke it before that (`Tracks`).

namespace Aoc.Year2020.Day15.Proofs
import Aoc.Year2020.Day15 (..)
import Aoc.Year2020.Day15 (Spec)
import Std (Bool, DecEq, Eq, List, Map, Nat, NonEmptyList, Option, Void)

--| `game` is the game the spec has played in `spoken` (the most recent first):
--| the same last number and number of turns, and a number's last turn
--| before the latest is the turn `turnsBack` counts back to.
def Tracks (game: Game) (spoken: List Nat): Prop :=
  ∃ (older: List Nat) =>
    spoken = [game.last, ..older] ∧ game.turn = older.length + 1
      ∧ ((number: Nat) → game.lastSeen.get number = (Spec.turnsBack number older).map (back => game.turn - back))

theorem turnsBackAtMost (number: Nat): (older: List Nat) → (back: Nat) → Spec.turnsBack number older = Some back → back ≤ older.length
  | [], back, found => Void.exfalso (Option.noneNotSome back found)
  | [spoken, ..older], back, found =>
    match same: spoken == number with
      | True => rewrite <- Option.someInjective found in rfl
      | False =>
        match inner: Spec.turnsBack number older with
          | None => Void.exfalso (Option.noneNotSome back found)
          | Some earlier =>
            let atMost := turnsBackAtMost number older earlier inner
            let isBack := Option.someInjective found
            omega

theorem beginTracks (first: Nat): Tracks (Game.begin first) [first] :=
  Witness [] (Both rfl (Both rfl (number => rfl)))

theorem mapShift (turn: Nat) (found: Option Nat): (found.map (turns => turns + 1)).map (back => (turn + 1) - back) = found.map (back => turn - back) :=
  match found with
    | None => rfl
    | Some back => rfl

theorem sayTracks (game: Game) (spoken: List Nat) (tracks: Tracks game spoken) (number: Nat): Tracks (game.say number) [number, ..spoken] :=
  match tracks with
    | Witness older (Both isSpoken (Both turns seen)) =>
      Witness spoken (Both rfl (Both (rewrite isSpoken in omega) (other =>
        rewrite isSpoken in
          match same: game.last == other with
            | True => rewrite <- DecEq.sound same, Map.getInsert in rfl
            | False => rewrite Map.getInsertOther game.last game.turn other (equal => DecEq.soundFalse game.last other same (Eq.sym equal)) game.lastSeen, seen other in Eq.sym (mapShift game.turn (Spec.turnsBack other older)))))

theorem replyTracks (game: Game) (spoken: List Nat) (tracks: Tracks game spoken): game.reply = Spec.reply spoken :=
  match tracks with
    | Witness older (Both isSpoken (Both turns seen)) =>
      rewrite isSpoken, seen game.last in
        match found: Spec.turnsBack game.last older with
          | None => rfl
          | Some back =>
            let atMost := turnsBackAtMost game.last older back found
            omega
