-- The keys: each arrow's bytes, as a terminal sends them, decode to that
-- arrow whatever follows (`arrowDecodes`, from std's `Key.nextBytes`), and
-- each arrow moves its way (`arrowMoves`); the letters, `.`, `>`, `p` and
-- `q` stand for what the keys line says (`documentedKeys`); and no other
-- key is a command (`onlyListedKeys`, `onlyCommandKeys`).

namespace Rogue.Proofs
import Rogue (..)
import Std (DecEq, Exists, Key, List, Option, Void)
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

-- No other printable key is a command: a key's command is the one
-- `keyCommands` lists beside it.
theorem onlyListedKeys (char: Char) (command: Command) (found: commandOfChar char = Some command): List.Mem (char, command) keyCommands :=
  let matches: (Char, Command) → Bool := (entry: (Char, Command)) => entry.fst == char
  match looked: keyCommands.find matches with
    | Some (key, listed) =>
      match List.findSome keyCommands matches (key, listed) looked with
        | Both same member =>
          let sameKey: key = char := DecEq.sound key char same
          let sameCommand: listed = command := Option.someInjective listed command found
          rewrite <- sameKey, <- sameCommand in member
    | None => Void.exfalso (Option.noneNotSome command found)

-- And no other key at all: a key that is a command is an arrow, or a
-- printable key listed with that command.
theorem onlyCommandKeys (key: Key) (command: Command) (found: commandOf key = Some command):
    Or (exists (direction: Direction) => key = arrow direction) (exists (char: Char) => And (key = Printable char) (List.Mem (char, command) keyCommands)) :=
  match key with
    | Up => Inl (Witness North rfl)
    | Down => Inl (Witness South rfl)
    | Left => Inl (Witness West rfl)
    | Right => Inl (Witness East rfl)
    | Printable char => Inr (Witness char (Both rfl (onlyListedKeys char command found)))
    | _ => Void.exfalso (Option.noneNotSome command found)
