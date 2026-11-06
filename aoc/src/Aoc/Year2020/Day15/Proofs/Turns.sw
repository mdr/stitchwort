--| Every turn the program takes is the spec's next turn, so the number it
--| gives for a turn is the spec's.

namespace Aoc.Year2020.Day15.Proofs
import Aoc.Year2020.Day15 (..)
import Aoc.Year2020.Day15 (Spec)
import Std (Eq, List, Nat, NonEmptyList)

--| `game` has played the spec's first `game.turn` turns.
def Playing (starting: Starting) (game: Game): Prop := Tracks game (Spec.spoken starting.numbers.toList game.turn)

theorem beginPlaying (starting: Starting): Playing starting (Game.begin starting.numbers.head) := beginTracks starting.numbers.head

theorem nextAgrees (starting: Starting) (game: Game) (playing: Playing starting game):
    starting.next game = (if game.turn < starting.numbers.toList.length then starting.numbers.toList.getOr game.turn 0 else Spec.reply (Spec.spoken starting.numbers.toList game.turn)) :=
  rewrite <- replyTracks game _ playing in rfl

theorem takeTurnPlaying (starting: Starting) (game: Game) (playing: Playing starting game): Playing starting (starting.takeTurn game) :=
  rewrite nextAgrees starting game playing in sayTracks game _ playing _

theorem lastTracks (game: Game) (spoken: List Nat) (tracks: Tracks game spoken): spoken.headOr 0 = game.last :=
  match tracks with
    | Witness older (Both isSpoken rest) => rewrite isSpoken in rfl

theorem iterateTurn (starting: Starting): (count: Nat) → (game: Game) → (Nat.iterate count starting.takeTurn game).turn = game.turn + count
  | Zero, game => omega
  | Succ count, game => rewrite iterateTurn starting count (starting.takeTurn game) in omega

theorem numberSpokenSpec (starting: Starting): (turn: Nat) → starting.numberSpoken turn = Spec.numberSpoken starting.numbers.toList turn
  | Zero => rfl
  | Succ later =>
    let final := Nat.iterate later starting.takeTurn (Game.begin starting.numbers.head)
    let playing: Playing starting final := Nat.iterateKeeps starting.takeTurn (Playing starting) (takeTurnPlaying starting) later _ (beginPlaying starting)
    -- Not `rewrite iterateTurn … in omega`: that is E-OMEGA-INTERNAL (aoc/NOTES-2020.md, day 15).
    let turns: final.turn = Succ later := Eq.trans (iterateTurn starting later _) (Nat.addComm 1 later)
    Eq.trans (Eq.sym (lastTracks final _ playing)) (Eq.cong (Spec.numberSpoken starting.numbers.toList) turns)
