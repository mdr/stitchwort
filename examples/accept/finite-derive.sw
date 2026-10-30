-- A derived `Finite` instance (docs/proposals/decide.md §6.2, SW-807): every
-- data type or record whose fields all have one, and that isn't recursive,
-- gets `Finite.all`, a list of every value, and `Finite.complete`, the proof
-- that every value is on it. The list is the constructors in the order
-- they're declared, each with every value of its fields, the first field
-- varying slowest.
import Std (List)

-- An enumeration: its constructors.
type Direction =
  | Up
  | Down
  | Left
  | Right

theorem directions: Finite.all = [Up, Down, Left, Right] := rfl

-- A constructor with a field: every arrow, then `Activate` (day 21's keys).
type DirectionKey =
  | Arrow (direction: Direction)
  | Activate

theorem directionKeys: Finite.all = [Arrow Up, Arrow Down, Arrow Left, Arrow Right, Activate] := rfl

-- Every key is on the list: the derived proof, nothing to write.
theorem everyKey (key: DirectionKey): key ∈ (Finite.all: List DirectionKey) := Finite.complete key

-- Fields of the library's finite types: `Bool`, `Ordering`, an `Option` and a
-- pair of them, and the program's own.
type Signal =
  | Off
  | Blink (colour: Ordering) (fast: Bool)
  | Point (aim: Option Direction)
  | Both (keys: (DirectionKey, Bool))

theorem signals: (Finite.all: List Signal).length = 1 + 3 * 2 + (1 + 4) + 5 * 2 := rfl

theorem signalsStart: (Finite.all: List Signal).take 4 = [Off, Blink Less False, Blink Less True, Blink Equal False] := rfl

theorem pointIn (aim: Option Direction): Point aim ∈ (Finite.all: List Signal) := Finite.complete (Point aim)

-- A record: one constructor, every combination of its fields.
type Switches = { power: Bool, light: Bool, mode: Ordering }

theorem switches: (Finite.all: List Switches).length = 12 := rfl

-- A type parameter needs a `Finite` instance for it.
type Slot (a: Type) =
  | Filled (value: a)
  | Empty

theorem slots: Finite.all = [Filled False, Filled True, Empty] := rfl

theorem slotsOfSlots: (Finite.all: List (Slot (Slot Direction))).length = 6 := rfl

-- The order is the derived `<`'s.
theorem sorted: List.sort (Finite.all: List DirectionKey) = Finite.all := rfl
