-- The keys: each arrow's bytes, as a terminal sends them, decode to that
-- arrow whatever follows (`arrowDecodes`, from std's `Key.nextBytes`), and
-- each arrow moves its way (`arrowMoves`); the letters, `.`, `>`, `p` and
-- `q` stand for what the keys line says (`documentedKeys`); and no other
-- key is a command (`onlyListedKeys`, `onlyCommandKeys`).

namespace Rogue.Proofs
import Rogue (..)
import Std (Decidable, Exists, Key, List, Option, Void)
import Std.Key (Up, Down, Left, Right, Printable)
import Std.Key.Decoded (Got)

-- The arrow key for each direction.
def arrow: Direction → Key
  | North => Up
  | South => Down
  | West => Left
  | East => Right

-- Each arrow moves its way.
theorem arrowMoves: (direction: Direction) → commandOf (arrow direction) = Some (Move direction)
  | North => rfl
  | South => rfl
  | West => rfl
  | East => rfl

-- The bytes a terminal sends for an arrow decode to that arrow, whatever follows.
theorem arrowDecodes (rest: List Nat): (direction: Direction) → Key.next (Key.bytes (arrow direction) ++ rest) = Got (arrow direction) rest
  | North => Key.nextBytes rest Up rfl
  | South => Key.nextBytes rest Down rfl
  | West => Key.nextBytes rest Left rfl
  | East => Key.nextBytes rest Right rfl

-- The keys as the help line names them.
theorem documentedKeys:
    ['k', 'w', 'j', 's', 'h', 'a', 'l', 'd', '.', '>', 'p', 'q'].map commandOfChar = [
      Some (Move North),
      Some (Move North),
      Some (Move South),
      Some (Move South),
      Some (Move West),
      Some (Move West),
      Some (Move East),
      Some (Move East),
      Some Wait,
      Some Descend,
      Some Drink,
      Some Quit
    ] :=
  rfl

-- The printable keys that are commands, as the keys line names them.
def commandKeys: List Char := ['h', 'j', 'k', 'l', 'a', 's', 'w', 'd', '.', '>', 'p', 'q']

-- A key in `commandKeys`, decided: in each arm below the key is a literal,
-- so the decision computes to `Yes`. (Not an `auto` argument: `auto`
-- searches at most 8 deep, and `'w'` is the 7th key.)
theorem listedKey (char: Char) (yes: Decidable.IsYes (List.decMem char commandKeys)): char ∈ commandKeys :=
  Decidable.fromYes (List.decMem char commandKeys) yes

-- No other printable key is a command: a printable key that is a command
-- is one of h/j/k/l, a/s/w/d, `.`, `>`, `p` and `q`. By the same match as
-- `commandOfChar`'s: in the `_` arm the key is none of those, so
-- `commandOfChar` takes its `_` arm too.
theorem onlyListedKeys (char: Char) (command: Command) (found: commandOfChar char = Some command): char ∈ commandKeys :=
  match char with
    | 'k' | 'w' | 'j' | 's' | 'h' | 'a' | 'l' | 'd' | '.' | '>' | 'p' | 'q' => listedKey char Trivial
    | _ => Void.exfalso (Option.noneNotSome command found)

-- And no other key at all: a key that is a command is an arrow, or one of
-- those printable keys.
theorem onlyCommandKeys (key: Key) (command: Command) (found: commandOf key = Some command):
    Or (exists (direction: Direction) => key = arrow direction) (exists (char: Char) => And (key = Printable char) (char ∈ commandKeys)) :=
  match key with
    | Up => Inl (Witness North rfl)
    | Down => Inl (Witness South rfl)
    | Left => Inl (Witness West rfl)
    | Right => Inl (Witness East rfl)
    | Printable char => Inr (Witness char (Both rfl (onlyListedKeys char command found)))
    | _ => Void.exfalso (Option.noneNotSome command found)
