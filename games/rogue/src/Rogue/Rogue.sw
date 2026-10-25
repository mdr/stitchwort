-- A small roguelike: go down three levels and take the amulet, past
-- goblins, orcs and trolls. Press h/j/k/l, a/s/w/d or the arrow keys to
-- move, > to go down stairs, p to drink a potion, . to wait, q to quit;
-- walking into a monster attacks it, and walking onto an item picks it up.
--
--   $ cd games/rogue && stitchwort run Rogue.main
--
-- The game is a pure core (Model.sw, Level.sw, Turn.sw, Render.sw), a
-- level generator (Generate.sw), and a thin shell (this file and Input.sw):
-- `play` reads a key, runs a turn, and draws the frame, until the game is
-- over. Keys and frames go through std's `Terminal`, run on the console by
-- `Terminal.toIO`; randomness is an ability of the game's own (Random.sw),
-- handled by a generator seeded from `IO.randomSeed`. Invariants of a turn
-- and of the generator are proved in `Rogue.Proofs`, and the tests are in
-- `Rogue.Tests`.

namespace Rogue
import Std (IO, List, Terminal, Text)

-- A different game each run: the host's random seed, cut to the
-- generator's 31 bits.
def main(): {IO, Partial} () :=
  let seed := IO.randomSeed() % 2147483648
  IO.print (ending (playOn seed))

-- A whole game on the console from a seed, until it's won, lost or given
-- up. The terminal is back to normal when this returns.
def playOn (seed: Nat): {IO, Partial} State := Terminal.toIO (() => seeded seed (() => playGame (newGame())))

def playGame (state: State): {Terminal, Random, Partial} State :=
  Terminal.draw (frame state)
  play state

-- One turn per command, until the game is won, lost or given up.
def play (state: State): {Terminal, Random, Partial} State :=
  if state.phase == Playing then play (playTurn state) else state

-- One key: a turn, and its frame, if the key is a command. Keys that aren't
-- commands are skipped, and the end of the input gives up. It is total, so
-- what a turn does on the terminal is proved about (Proofs/Loop.sw).
def playTurn (state: State): {Terminal, Random} State :=
  match nextCommand() with
    | None => state
    | Some command =>
      let next := step state command
      Terminal.draw (frame next)
      next

def ending (state: State): Text :=
  match state.phase with
    | Won => "You won on turn ${state.turn} with ${state.hitPoints} hit points."
    | Died => "You died on level ${state.level.depth}, on turn ${state.turn}."
    | GaveUp => "You gave up on level ${state.level.depth}, on turn ${state.turn}."
    | Playing => "The game stopped while still playing."
