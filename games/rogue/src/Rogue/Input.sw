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

-- The command of a printable key, if any.
def commandOfChar (char: Char): Option Command :=
  match char with
    | 'k' | 'w' => Some (Move North)
    | 'j' | 's' => Some (Move South)
    | 'h' | 'a' => Some (Move West)
    | 'l' | 'd' => Some (Move East)
    | '.' => Some Wait
    | '>' => Some Descend
    | 'p' => Some Drink
    | 'q' => Some Quit
    | _ => None

-- The next key's command: `None` for a key that isn't one (`Unknown`
-- included), and `Quit` at the end of the input.
def nextCommand(): {Terminal} (Option Command) :=
  match Terminal.readKey() with
    | None => Some Quit
    | Some key => commandOf key
