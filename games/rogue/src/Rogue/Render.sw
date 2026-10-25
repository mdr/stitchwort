-- Drawing the game as lines of text: the level, then a status line, the
-- keys, and the turn's message.

namespace Rogue
import Std (List, Option, Text)

def render (state: State): List Text :=
  let map := state.level.terrain.withIndex.map (((row, chars)) =>
    let marks := marksIn state row
    chars.withIndex.map (((column, char)) => glyphAt marks column char) |> Text.fromList)
  map ++ [statusLine state, keysLine, state.message]

-- What stands on a row, by column: the player first, then monsters, then
-- items, so that the first mark of a column is the one drawn.
def marksIn (state: State) (row: Nat): List (Nat, Char) :=
  let player := if state.player.row == row then [(state.player.column, '@')] else []
  let monsters := state.monsters.filterMap (monster => if monster.position.row == row then Some (monster.position.column, monster.kind.glyph) else None)
  let items := state.items.filterMap (item => if item.position.row == row then Some (item.position.column, item.loot.glyph) else None)
  player ++ monsters ++ items

def glyphAt (marks: List (Nat, Char)) (column: Nat) (terrain: Char): Char :=
  match marks.find (mark => mark.fst == column) with
    | Some (_, glyph) => glyph
    | None => terrain

def statusLine (state: State): Text :=
  "Level ${state.level.depth}/${deepest}   HP ${state.hitPoints}/${maxHitPoints}   Potions ${state.potions}   Blows 2-${state.strength}   Turn ${state.turn}"

-- The keys, under the status line.
def keysLine: Text := "h/j/k/l or a/s/w/d move   . waits   > goes down   p drinks a potion   q quits"
