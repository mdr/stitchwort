--| The game follows the spec turn by turn: after each turn, its last number
--| is the spec's latest and its array gives, for every number it has room
--| for, the turn the spec last spoke it before that, or 0 (`Tracks`).

namespace Aoc.Year2020.Day15.Proofs
import Aoc.Year2020.Day15 (..)
import Aoc.Year2020.Day15 (Spec)
import Std (Array, Bool, DecEq, Eq, List, Nat, NonEmptyList, Option, Void)

--| `game` is the game the spec has played in `spoken` (the most recent first):
--| the same last number and number of turns, the last number has room in
--| the array, and a number's entry is the turn `turnsBack` counts back to,
--| or 0 if it wasn't spoken before the latest turn.
def Tracks (game: Game) (spoken: List Nat): Prop :=
  ∃ (older: List Nat) =>
    spoken = [game.last, ..older] ∧ game.turn = older.length + 1 ∧ game.last < game.lastSeen.size
      ∧ (∀ (number: Nat) => number < game.lastSeen.size →
        game.lastSeen.getOr number 0 = ((Spec.turnsBack number older).map (back => game.turn - back)).getOrElse 0)

theorem turnsBackAtMost (number: Nat) (older: List Nat) (back: Nat) (found: Spec.turnsBack number older = Some back): back ≤ older.length :=
  match older with
    | [spoken, ..older] =>
      match same: spoken == number with
        | True => rewrite <- Option.someInjective found in rfl
        | False =>
          match inner: Spec.turnsBack number older with
            | Some earlier =>
              let atMost := turnsBackAtMost number older earlier inner
              let isBack := Option.someInjective found
              omega

theorem beginTracks (room: Nat) (first: Nat) (fits: first < room): Tracks (Game.begin room first) [first] :=
  Witness [] (Both rfl (Both rfl (Both (rewrite Array.sizeReplicate room 0 in fits) (number inside => Array.getOrReplicate room 0 number))))

theorem mapShift (turn: Nat) (found: Option Nat): (found.map (turns => turns + 1)).map (back => (turn + 1) - back) = found.map (back => turn - back) :=
  match found with
    | None => rfl
    | Some back => rfl

theorem sayTracks (game: Game) (spoken: List Nat) (tracks: Tracks game spoken) (number: Nat) (fits: number < game.lastSeen.size):
    Tracks (game.say number) [number, ..spoken] :=
  match tracks with
    | Witness older (Both isSpoken (Both turns (Both lastFits seen))) =>
      let sized := Array.sizeSet game.lastSeen game.last game.turn
      Witness spoken (Both rfl (Both (rewrite isSpoken in omega) (Both (rewrite sized in fits) (other inside =>
        rewrite isSpoken in
          match same: game.last == other with
            | True => rewrite <- DecEq.sound same, Array.getOrSet game.lastSeen game.last game.turn 0 lastFits in rfl
            | False =>
              rewrite Array.getOrSetOther game.lastSeen game.last game.turn other 0 (equal => DecEq.soundFalse game.last other same (Eq.sym equal)),
                seen other (rewrite sized at inside in inside)
              in Eq.cong (found => Option.getOrElse found 0) (Eq.sym (mapShift game.turn (Spec.turnsBack other older)))))))

theorem replyTracks (game: Game) (spoken: List Nat) (tracks: Tracks game spoken): game.reply = Spec.reply spoken :=
  match tracks with
    | Witness older (Both isSpoken (Both turns (Both lastFits seen))) =>
      rewrite isSpoken in
        match found: Spec.turnsBack game.last older with
          | None => rewrite seen game.last lastFits, found in rfl
          | Some back =>
            let atMost := turnsBackAtMost game.last older back found
            rewrite seen game.last lastFits, found in
              match zero: (game.turn - back) == 0 with
                | True => omega
                | False => omega

--| A reply is less than the turn it answers.
theorem replyBelow (game: Game) (spoken: List Nat) (tracks: Tracks game spoken): game.reply < game.turn :=
  match tracks with
    | Witness older (Both isSpoken (Both turns (Both lastFits seen))) =>
      rewrite replyTracks game spoken tracks, isSpoken in
        match found: Spec.turnsBack game.last older with
          | None => omega
          | Some back =>
            let atMost := turnsBackAtMost game.last older back found
            omega
