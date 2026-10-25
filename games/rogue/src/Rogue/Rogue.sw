-- A small roguelike: find the stairs (>) before the goblins and orcs find
-- you. Type h/j/k/l (or a/s/w/d) and Enter to move, . to wait, q to quit;
-- walking into a monster attacks it.
--
--   $ cd games/rogue && stitchwort run Rogue.main
--
-- The game is a pure core (Model.sw, Dungeon.sw, Turn.sw, Render.sw) and a
-- thin shell (this file): `play` reads a command, runs a turn, and draws the
-- frame. Randomness and input are abilities (Random.sw, Input.sw), handled
-- here by a seeded generator and by standard input. Invariants of a turn
-- are proved in `Rogue.Proofs`, and the tests are in `Rogue.Tests`.

namespace Rogue
import Std (List, Text)

def main(): {IO} () :=
  let final := fromLines (() => seeded defaultSeed (() => playGame initialState))
  IO.print (ending final)

-- There is no clock or other source of entropy to seed from, so every game
-- starts from the same seed.
def defaultSeed: Nat := 2026

-- The most turns a game lasts. The loop is bounded, not `Partial`, so that
-- the handlers above (and `IO.simulate` in the tests) can wrap it.
def maxTurns: Nat := 100000

def playGame (state: State): {IO, Input, Random} State :=
  draw state
  play maxTurns state

def play: Nat → State → {IO, Input, Random} State
  | 0, state => state
  | Succ remaining, state =>
    if state.phase == Playing then
      let command := nextCommand()
      let next := step state command
      draw next
      play remaining next
    else state

-- The ANSI escapes that clear the screen and move to its top-left corner.
def clearScreen: Text := "\u{1b}[2J\u{1b}[H"

-- One frame, printed at once. `IO.print` ends it with a line ending, so the
-- cursor waits below the message.
def draw (state: State): {IO} () := IO.print (clearScreen ++ Text.join (render state) '\n')

def ending (state: State): Text :=
  match state.phase with
    | Escaped => "You escaped on turn ${state.turn} with ${state.hitPoints} hit points."
    | Died => "You died on turn ${state.turn}."
    | GaveUp => "You gave up on turn ${state.turn}."
    | Playing => "The game ran out of turns."
