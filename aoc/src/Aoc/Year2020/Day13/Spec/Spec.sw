--| Day 13 as the puzzle states it, about the notes (the program's `Notes`:
--| the earliest time you could leave, and the schedule of `Slot`s): how the
--| notes are written, when a bus departs, and each part's answer. Nothing
--| else is shared with the program. The proofs (Proofs/) show the program
--| computes these.

namespace Aoc.Year2020.Day13.Spec
import Aoc.Year2020.Day13 (Notes, Slot)
import Std (Char, List, NonEmptyList, Parse)

-- The format

--| A bus ID in decimal, at least 1 (it is how often the bus leaves), or
--| "x" for a bus out of service.
def SlotWritten (read: List Char) (slot: Slot): Prop := match slot with
  | Listed id => read ≠ [] ∧ read.all Parse.isDigit = True ∧ id = Parse.digitsValue read ∧ id ≠ 0
  | OutOfService => read = ['x']

--| "The first line is your estimate of the earliest timestamp you could
--| depart on a bus. The second line lists the bus IDs that are in service
--| according to the shuttle company; entries that show x must be out of
--| service": the timestamp in decimal, a line break, and the entries
--| separated by commas.
def NotesWritten (read: List Char) (notes: Notes): Prop :=
  ∃ (digits: List Char) => ∃ (lineBreak: List Char) => ∃ (entries: List Char) => ∃ (slots: NonEmptyList Slot) =>
    read = digits ++ lineBreak ++ entries
      ∧ digits ≠ [] ∧ digits.all Parse.isDigit = True ∧ notes.earliest = Parse.digitsValue digits
      ∧ Parse.LineBreak lineBreak
      ∧ Parse.SepBy SlotWritten (read u => read = [',']) entries slots ∧ notes.schedule = slots.toList

-- Departures

--| "Each bus has an ID number that also indicates how often the bus leaves
--| for the airport": "the bus with ID 5 departs from the sea port at
--| timestamps 0, 5, 10, 15, and so on".
def Departs (id: Nat) (time: Nat): Prop := ∃ (trips: Nat) => time = trips * id

-- Part 1

--| "What is the ID of the earliest bus you can take to the airport
--| multiplied by the number of minutes you'll need to wait for that bus?":
--| a bus in service that departs at or after the earliest time you could
--| leave, when no bus in service departs between. If two buses leave at
--| that same minute the puzzle doesn't say which to take, and either's
--| answer is one here.
def Part1 (notes: Notes) (answer: Nat): Prop :=
  ∃ (id: Nat) => ∃ (departure: Nat) =>
    Listed id ∈ notes.schedule ∧ Departs id departure ∧ notes.earliest ≤ departure
      ∧ (∀ (other time: Nat) => Listed other ∈ notes.schedule → Departs other time → notes.earliest ≤ time → departure ≤ time)
      ∧ answer = id * (departure - notes.earliest)

-- Part 2

--| "The first bus ID departs at that time and each subsequent listed bus
--| ID departs at that subsequent minute"; "an x in the schedule means there
--| are no constraints on what bus IDs must depart at that time".
def LinedUp: (schedule: List Slot) → (time: Nat) → Prop
  | [], time => Unit
  | [Listed id, ..rest], time => Departs id time ∧ LinedUp rest (time + 1)
  | [OutOfService, ..rest], time => LinedUp rest (time + 1)

--| "What is the earliest timestamp such that all of the listed bus IDs
--| depart at offsets matching their positions in the list?"
def Part2 (notes: Notes) (answer: Nat): Prop :=
  LinedUp notes.schedule answer ∧ (∀ (time: Nat) => LinedUp notes.schedule time → answer ≤ time)
