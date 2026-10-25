-- Input, behind an ability of its own so the way keys are read can change
-- without touching the game: for now, lines typed and ended with Enter,
-- each character one command.

namespace Rogue
import Std (List, Text)

ability Input where
  nextCommand: () → {Input} Command

-- The command a key stands for, if any.
def commandOf (key: Char): Option Command :=
  match key with
    | 'k' => Some (Move North)
    | 'w' => Some (Move North)
    | 'j' => Some (Move South)
    | 's' => Some (Move South)
    | 'h' => Some (Move West)
    | 'a' => Some (Move West)
    | 'l' => Some (Move East)
    | 'd' => Some (Move East)
    | '.' => Some Wait
    | 'q' => Some Quit
    | _ => None

-- Answers `nextCommand` from the lines of standard input: the commands of a
-- line are used up before the next line is read, keys that aren't commands
-- are skipped, and the end of the input is `Quit`.
def fromLines (prog: () → {Input, IO | e} a): {IO | e} a :=
  let run: List Command → {IO | e} a :=
    handle prog() with
      | return result => _ => result
      | nextCommand (), resume => pending =>
        let (command, rest) := nextFrom pending
        resume command rest
  run []

-- The next command and the ones left over, reading lines while none are
-- pending. Bounded by the input: `readLine` gives `None` at its end.
def nextFrom (pending: List Command): {IO} (Command, List Command) :=
  match pending with
    | Cons command rest => (command, rest)
    | [] => readCommands linesPerCommand

-- How many lines without a command to skip before giving up (a total
-- bound: the input itself would do, but `readLine` doesn't promise to end).
def linesPerCommand: Nat := 1000

def readCommands: Nat → {IO} (Command, List Command)
  | 0 => (Quit, [])
  | Succ remaining =>
    match IO.readLine() with
      | None => (Quit, [])
      | Some line =>
        match line.toList.filterMap commandOf with
          | Cons command rest => (command, rest)
          | [] => readCommands remaining
