--| Settling a choice for every position by elimination, shared between days.
--| Each position has candidates (the values it could take); a value can be
--| taken at one position only. A position with a single candidate left, once
--| the values taken elsewhere are left out, takes it, and that may leave
--| another position with one candidate, and so on. The proofs are in
--| `Aoc.Common.Proofs` (Proofs/Elimination.sw): what `assign` finds takes a
--| candidate at each position and no value twice, and it is the only way to.

namespace Aoc.Common
import Std (DecEq, List, Option)

--| A position while the choices are being worked out: the values it could
--| take, fixed, and the value settled for it, if any.
type Slot (a: Type) = { candidates: List a, choice: Option a }

--| A position with nothing settled yet.
def Slot.open (candidates: List a): Slot a := { candidates, choice = None }

--| The values settled so far, in the order of their positions.
def chosen (slots: List (Slot a)): List a := slots.filterMap .choice

--| The values this position could still take, leaving out those in `taken`.
def Slot.remaining [auto eq: DecEq a] (slot: Slot a) (taken: List a): List a :=
  slot.candidates.filter (value => not (taken.contains value))

--| Settles the first position not yet settled that has one value left, or
--| `None` if there is none.
def settle [auto eq: DecEq a] (taken: List a): List (Slot a) → Option (List (Slot a))
  | [] => None
  | [slot, ..slots] =>
    match slot.choice with
      | Some _ => (settle taken slots).map (Cons slot)
      | None =>
        match slot.remaining taken with
          | [value] => Some [{ slot | choice = Some value }, ..slots]
          | _ => (settle taken slots).map (Cons slot)

--| Every position's value, if every position is settled.
def allSettled: List (Slot a) → Option (List a)
  | [] => Some []
  | [slot, ..slots] =>
    match slot.choice with
      | Some value => (allSettled slots).map (Cons value)
      | None => None

--| Settles positions one at a time until all are, in at most `rounds`
--| rounds (each settles one, so as many rounds as positions are enough);
--| `None` when a round finds no position with one value left.
def eliminate [auto eq: DecEq a] (rounds: Nat) (slots: List (Slot a)): Option (List a) := match allSettled slots with
  | Some values => Some values
  | None =>
    match rounds with
      | Zero => None
      | Succ more =>
        match settle (chosen slots) slots with
          | Some next => eliminate more next
          | None => None

--| The value taken at each position, given each position's candidates, if
--| the elimination settles every position.
def assign [auto eq: DecEq a] (candidates: List (List a)): Option (List a) :=
  eliminate candidates.length (candidates.map Slot.open)
