-- The keys: each arrow's bytes, as a terminal sends them, decode to that
-- arrow whatever follows (`arrowDecodes`, from std's `Key.nextBytes`), and
-- each arrow moves its way (`arrowMoves`); the letters, `.`, `>`, `p` and
-- `q` stand for what the keys line says (`documentedKeys`).

namespace Rogue.Proofs
import Rogue (..)
import Std (Key, List)
import Std.Key (Up, Down, Left, Right)
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
