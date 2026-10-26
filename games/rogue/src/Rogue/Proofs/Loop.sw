-- One turn of the real loop, `playTurn`, under the test handlers
-- `Terminal.simulate` and `Random.withSeed`: a key that is a command runs `resolve`
-- with the seed's dice and draws its frame (`turnKey`); any other key does
-- nothing (`turnOther`); the end of the keys gives up (`turnEnd`). So every
-- turn the loop takes keeps the state valid (`turnValid`), and pressing an
-- arrow walks that way (`arrowWalks`).
--
-- `play` repeats `playTurn` until the game is over. It is partial, and a
-- partial program under a handler has nothing to prove about it
-- (docs/proposals/partial-handlers.md §3.5), so the loop as a whole is
-- covered by `replayValid` (Game.sw) over the turns it takes.

namespace Rogue.Proofs
import Rogue (..)
import Std (Ansi, Key, List, Nat, Option, Pair, Terminal)

theorem turnKey (seed: Nat) (state: State) (key: Key) (rest: List Key) (command: Command) (isCommand: commandOf key = Some command):
    let after := resolve { seed = lcg seed / 65536 } state command
    Terminal.simulate (Cons key rest) (() => Random.withSeed seed (() => playTurn state)) = MkPair [frame after |> .map Ansi.strip] after :=
  rewrite isCommand in rfl

theorem turnOther (seed: Nat) (state: State) (key: Key) (rest: List Key) (notCommand: commandOf key = None):
    Terminal.simulate (Cons key rest) (() => Random.withSeed seed (() => playTurn state)) = MkPair [] state :=
  rewrite notCommand in rfl

theorem turnEnd (seed: Nat) (state: State):
    let after := resolve { seed = lcg seed / 65536 } state Quit
    Terminal.simulate [] (() => Random.withSeed seed (() => playTurn state)) = MkPair [frame after |> .map Ansi.strip] after :=
  rfl

theorem turnValid (seed: Nat) (state: State) (valid: Valid state):
    (keys: List Key) → Valid (Terminal.simulate keys (() => Random.withSeed seed (() => playTurn state))).snd
  | [] => resolveValid { seed = lcg seed / 65536 } state Quit valid
  | Cons key rest =>
    match isCommand: commandOf key with
      | Some command => resolveValid { seed = lcg seed / 65536 } state command valid
      | None => valid

-- So pressing an arrow, in the real turn under the test handlers, walks that way.
theorem arrowWalks (seed: Nat) (state: State) (direction: Direction) (rest: List Key) (playing: state.phase = Playing)
    (vacant: monsterAt (state.player.toward direction) state.monsters = None) (open: isWall state.level (state.player.toward direction) = False):
    (Terminal.simulate (Cons (arrow direction) rest) (() => Random.withSeed seed (() => playTurn state))).snd.player = state.player.toward direction :=
  rewrite turnKey seed state (arrow direction) rest (Move direction) (arrowMoves direction) in
    resolveMoves { seed = lcg seed / 65536 } state direction playing vacant open
