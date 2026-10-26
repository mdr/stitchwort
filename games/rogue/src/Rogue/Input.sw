-- Input: the command each key stands for, read one keypress at a time from
-- std's `Terminal`.

namespace Rogue
import Std (Key, Terminal)
import Std.Key (Printable, Up, Down, Left, Right)

-- The command a key stands for, if any: the arrows, h/j/k/l and a/s/w/d
-- move; `.` waits, `>` goes down, `p` drinks and `q` quits.
def commandOf (key: Key): Option Command :=
  match key with
    | Up => Some (Move North)
    | Down => Some (Move South)
    | Left => Some (Move West)
    | Right => Some (Move East)
    | Printable char => commandOfChar char
    | _ => None

-- The command of a printable key: the one `keyCommands` lists for it, if any.
-- (A table rather than a `match` on characters, so that "no other key is a
-- command" can be proved: `onlyListedKeys`, Proofs/Input.sw.)
def commandOfChar (char: Char): Option Command :=
  keyCommands.find ((entry: (Char, Command)) => entry.fst == char) |> .map (.snd)

def keyCommands: List (Char, Command) := [
  ('k', Move North),
  ('w', Move North),
  ('j', Move South),
  ('s', Move South),
  ('h', Move West),
  ('a', Move West),
  ('l', Move East),
  ('d', Move East),
  ('.', Wait),
  ('>', Descend),
  ('p', Drink),
  ('q', Quit)
]

-- The next key's command: `None` for a key that isn't one (`Unknown`
-- included), and `Quit` at the end of the input.
def nextCommand(): {Terminal} (Option Command) :=
  match Terminal.readKey() with
    | None => Some Quit
    | Some key => commandOf key
