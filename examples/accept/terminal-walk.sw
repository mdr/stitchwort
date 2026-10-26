-- A walking `@`: h, j, k, l or the arrow keys move it round a small room,
-- and q stops (docs/proposals/terminal-io.md). The game reads keys and
-- draws whole frames through `Terminal`; `Terminal.toIO` runs it on the
-- console, and `Terminal.simulate` runs it in the tests below.
--
--   $ printf 'llj\033[Bq' | stitchwort run examples/accept/terminal-walk.sw

import Std (Ansi, IO, Key, List, Nat, Pair, Terminal, Text)
import Std.Key (Printable, Up, Down, Left, Right)
import Std.Ansi.Colour (Yellow)

-- Where the `@` is: a column and a row inside the room.
type Position = { column: Nat, row: Nat }

def roomWidth: Nat := 10
def roomHeight: Nat := 4

def start: Position := { column = 0, row = 0 }

-- The position a key moves to; a key that isn't a move, or a move into a
-- wall, stays put.
def move (position: Position) (key: Key): Position :=
  match key with
    | Printable 'h' => left position
    | Left => left position
    | Printable 'l' => right position
    | Right => right position
    | Printable 'k' => up position
    | Up => up position
    | Printable 'j' => down position
    | Down => down position
    | _ => position

def left (position: Position): Position := { column = Nat.pred position.column, row = position.row }
def right (position: Position): Position := { column = Nat.min (position.column + 1) (roomWidth - 1), row = position.row }
def up (position: Position): Position := { column = position.column, row = Nat.pred position.row }
def down (position: Position): Position := { column = position.column, row = Nat.min (position.row + 1) (roomHeight - 1) }

-- The screen: the room in a wall of `#`, then a line of help.
def view (position: Position): List Text :=
  let wall := Text.repeat "#" (roomWidth + 2)
  let rows := List.range roomHeight |> .map (row => "#${rowText position row}#")
  List.append (Cons wall (List.append rows [wall])) ["hjkl or arrows to move, q to stop"]

def rowText (position: Position) (row: Nat): Text :=
  if row == position.row then
    "${Text.repeat "." position.column}${Ansi.colour Yellow "@"}${Text.repeat "." (roomWidth - 1 - position.column)}"
  else Text.repeat "." roomWidth

-- One frame and one key per step, until q or the end of the keys. The
-- fuel bounds the steps, since the loop must be total for now: once
-- handlers can run partial code (docs/proposals/partial-handlers.md), it
-- goes, `walk` becomes `{Terminal, Partial}`, and so does `main`.
def walk: Nat → Position → {Terminal} Position
  | 0, position => position
  | Succ fuel, position =>
    Terminal.draw (view position)
    match Terminal.readKey () with
      | None => position
      | Some (Printable 'q') => position
      | Some key => walk fuel (move position key)

def steps: Nat := 100000

def main (): {IO} () :=
  let final := Terminal.toIO (() => walk steps start)
  IO.print "The @ stopped at column ${final.column}, row ${final.row}."

-- Tests

def finalOf (keys: List Key): Position := Pair.snd (Terminal.simulate keys (() => walk steps start))

test "the arrows and hjkl move" := finalOf [Right, Printable 'l', Down, Printable 'j', Printable 'h'] == { column = 1, row = 2 }
test "walls stop it" := finalOf [Up, Left, Printable 'k', Printable 'h'] == start
test "the far walls too" := finalOf (List.replicate 20 Right ++ List.replicate 20 Down) == { column = 9, row = 3 }
test "other keys do nothing" := finalOf [Printable 'x', Key.Enter, Key.Unknown, Right] == { column = 1, row = 0 }
test "q stops it" := finalOf [Right, Printable 'q', Right] == { column = 1, row = 0 }

test "one frame per key, and one at the start" :=
  let (frames, final) := Terminal.simulate [Right, Down, Printable 'q'] (() => walk steps start)
  List.length frames == 3 && List.map frames (frame => List.map frame Ansi.strip) == [
    ["############", "#@.........#", "#..........#", "#..........#", "#..........#", "############", "hjkl or arrows to move, q to stop"],
    ["############", "#.@........#", "#..........#", "#..........#", "#..........#", "############", "hjkl or arrows to move, q to stop"],
    ["############", "#..........#", "#.@........#", "#..........#", "#..........#", "############", "hjkl or arrows to move, q to stop"]
  ]

-- The whole `main`, on piped input: the keys are decoded from the bytes
-- (an arrow's escape sequence included), and each frame is printed as
-- lines with a form feed after it.
test "main on piped input" :=
  let (printed, _) := IO.simulate ["ll\u{1b}[Bq"] main
  List.length (List.filter printed (line => line == "\u{c}")) == 4 &&
    List.last printed == Some "The @ stopped at column 2, row 1."
