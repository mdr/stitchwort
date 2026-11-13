--| Every turn the program takes is the spec's next turn, so the number it
--| gives for a turn is the spec's. Each turn's number has room in the array,
--| as long as the game is short of `Starting.room`'s count of turns.

namespace Aoc.Year2020.Day15.Proofs
import Aoc.Year2020.Day15 (..)
import Aoc.Year2020.Day15 (Spec)
import Std (Array, Eq, List, Nat, NonEmptyList, Option, Void)

--| `game` has played the spec's first `game.turn` turns, in an array of `room` numbers.
def Playing (starting: Starting) (room: Nat) (game: Game): Prop :=
  Tracks game (Spec.spoken starting.numbers.toList game.turn) ∧ game.lastSeen.size = room

--| A starting number is at most the largest; past the end, `getOr` gives 0.
theorem startingAtMost ∀ (starting: Starting) (i: Nat): starting.numbers.toList.getOr i 0 ≤ starting.numbers.toList.maximum.getOrElse 0 :=
  match below: i < starting.numbers.toList.length with
    | True =>
      let member := List.getOrMem starting.numbers.toList i 0 below
      match List.maximumExists starting.numbers.toList _ member with
        | Witness top most => rewrite Option.someInjective most in (List.maximumSome starting.numbers.toList top most).right _ member
    | False => rewrite List.getOrPast starting.numbers.toList i 0 (omega) in omega

theorem beginPlaying ∀ (starting: Starting) (turns: Nat):
    Playing starting (starting.room turns) (Game.begin (starting.room turns) starting.numbers.head) :=
  let atMost := startingAtMost starting 0
  Both (beginTracks (starting.room turns) starting.numbers.head (omega)) (Array.sizeReplicate (starting.room turns) 0)

theorem nextAgrees ∀ (starting: Starting) (room: Nat) (game: Game) (playing: Playing starting room game):
    starting.next game = (if game.turn < starting.numbers.toList.length then starting.numbers.toList.getOr game.turn 0 else Spec.reply (Spec.spoken starting.numbers.toList game.turn)) :=
  rewrite <- replyTracks game _ playing.left in rfl

--| Short of `room`'s count of turns, the next number has room.
theorem nextFits ∀ (starting: Starting) (turns: Nat) (game: Game) (playing: Playing starting (starting.room turns) game) (short: game.turn < turns):
    starting.next game < starting.room turns :=
  let reply := replyBelow game _ playing.left
  let atMost := startingAtMost starting game.turn
  match below: game.turn < starting.numbers.length with
    | True => omega
    | False => omega

theorem takeTurnPlaying ∀ (starting: Starting) (turns: Nat) (game: Game) (playing: Playing starting (starting.room turns) game) (short: game.turn < turns):
    Playing starting (starting.room turns) (starting.takeTurn game) :=
  let fits: starting.next game < game.lastSeen.size := rewrite playing.right in nextFits starting turns game playing short
  Both (rewrite nextAgrees starting (starting.room turns) game playing in sayTracks game _ playing.left _ (rewrite <- nextAgrees starting (starting.room turns) game playing in fits))
    (Eq.trans (Array.sizeSet game.lastSeen game.last game.turn) playing.right)

theorem lastTracks ∀ (game: Game) (spoken: List Nat) (tracks: Tracks game spoken): spoken.headOr 0 = game.last :=
  match tracks with
    | Witness older (Both isSpoken rest) => rewrite isSpoken in rfl

theorem iterateTurn ∀ (starting: Starting) (count: Nat) (game: Game): (Nat.iterate count starting.takeTurn game).turn = game.turn + count :=
  match count with
    | Zero => omega
    | Succ count => rewrite iterateTurn starting count (starting.takeTurn game) in omega

--| `count` more turns keep the game playing, as long as they end by `turns`.
theorem iteratePlaying ∀ (starting: Starting) (turns: Nat) (count: Nat) (game: Game)
    (playing: Playing starting (starting.room turns) game) (short: game.turn + count ≤ turns):
    Playing starting (starting.room turns) (Nat.iterate count starting.takeTurn game) := match count with
      | Zero => playing
      | Succ count =>
        iteratePlaying starting turns count (starting.takeTurn game) (takeTurnPlaying starting turns game playing (omega)) (omega)

theorem numberSpokenSpec ∀ (starting: Starting) (turn: Nat): starting.numberSpoken turn = Spec.numberSpoken starting.numbers.toList turn :=
  match turn with
    | Zero => rfl
    | Succ later =>
      let final := Nat.iterate later starting.takeTurn (Game.begin (starting.room (Succ later)) starting.numbers.head)
      let playing: Playing starting (starting.room (Succ later)) final :=
        iteratePlaying starting (Succ later) later _ (beginPlaying starting (Succ later)) (omega)
      -- Not `rewrite iterateTurn … in omega`: that is E-OMEGA-INTERNAL (aoc/NOTES-2020.md, day 15).
      let turns: final.turn = Succ later := Eq.trans (iterateTurn starting later _) (Nat.addComm 1 later)
      Eq.trans (Eq.sym (lastTracks final _ playing.left)) (Eq.cong (Spec.numberSpoken starting.numbers.toList) turns)
