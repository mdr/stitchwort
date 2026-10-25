-- Drawing the game as lines of text: the dungeon, then a status line and
-- the turn's message.

namespace Rogue
import Std (List, Text)

def render (state: State): List Text :=
  let map := dungeonRows.withIndex.map (((row, chars)) =>
    chars.withIndex.map (((column, char)) => glyphAt state { row, column } char) |> Text.fromList)
  map ++ [statusLine state, state.message]

-- What's drawn on a cell: the player, a monster, a potion, or the floor.
def glyphAt (state: State) (position: Position) (char: Char): Char :=
  if position == state.player then '@'
  else
    match monsterAt position state.monsters with
      | Some monster => monster.kind.glyph
      | None => if position ∈ state.potions then '!' else terrainOf char

def statusLine (state: State): Text :=
  "HP ${state.hitPoints}/${maxHitPoints}   Turn ${state.turn}   Monsters ${state.monsters.length}   (h/j/k/l or a/s/w/d move, . waits, q quits)"
