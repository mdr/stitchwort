--| Advent of Code 2020, day 13: your notes on the shuttle buses, the
--| earliest time you could leave on the first line, the bus schedule on the
--| second: bus IDs, and `x` for one out of service. A bus departs every
--| time that is a multiple of its ID. Part 1: the earliest bus you can take,
--| its ID times the minutes you wait for it. Part 2: the earliest time at
--| which the first listed bus departs, and each later one departs as many
--| minutes after it as it is further down the schedule.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day13.main < inputs/2020/day13.txt
--|
--| Part 2 is a sieve, one bus at a time: the times that suit the buses so
--| far are `time`, then every `period` minutes after. For the next bus it
--| steps through those to the first that suits that bus too, and on to the
--| next after it, whose distance is the new period (the lcm of the IDs so
--| far, measured rather than computed, so no ID needs to be coprime with
--| the others). The proofs, that the parser reads the puzzle's format and
--| that both answers are the puzzle's, are in `Aoc.Year2020.Day13.Proofs`
--| (Proofs/), and the tests in `Aoc.Year2020.Day13.Tests` (Tests/); `run`
--| checks neither.

namespace Aoc.Year2020.Day13
import Std (Fail, IO, List, Nat, NonEmptyList, Option, Parse)

def main(): {IO, Fail} () :=
  let notes := parseNotes IO.readAll()
  IO.print "Part 1: ${notes.earliestBus |> .orFail "no bus is in service"}"
  IO.print "Part 2: ${notes.earliestLineUp |> .orFail "the buses never line up"}"

--| One entry of the schedule.
type Slot =
  | Listed (id: Nat)
  | OutOfService

type Notes = { earliest: Nat, schedule: List Slot }

def slot(): {Parse} Slot := match Parse.optional (() => Parse.char 'x') with
  | Some _ => OutOfService
  | None =>
    let id := Parse.nat()
    if id == 0 then Parse.fail "a bus ID is at least 1" else Listed id

def notes(): {Parse} Notes :=
  let earliest := Parse.nat()
  Parse.newline()
  let schedule := Parse.sepBy1 slot (() => Parse.char ',')
  { earliest, schedule = schedule.toList }

def parseNotes (input: Text): {Fail} Notes := Parse.all input notes

--| A bus in service, and how far down the schedule it is.
type Bus = { id: Nat, offset: Nat }

def Slot.bus (slot: Slot) (offset: Nat): Option Bus := match slot with
  | Listed id => Some { id, offset }
  | OutOfService => None

def Notes.buses (notes: Notes): List Bus := notes.schedule.withIndex.filterMap (((offset, slot)) => slot.bus offset)

--| The first time at or after `from` that the bus departs.
def Bus.nextDeparture (bus: Bus) (from: Nat): Nat := Nat.ceilDiv from bus.id * bus.id

--| Part 1: the ID of the bus that leaves first from when you can leave,
--| times the minutes you wait for it.
def Notes.earliestBus (notes: Notes): Option Nat :=
  let departure := (bus: Bus) => bus.nextDeparture notes.earliest
  notes.buses.minimumOf departure
    |> .flatMap (first => notes.buses.find (bus => departure bus == first))
    |> .map (bus => bus.id * (departure bus - notes.earliest))

--| Whether the bus departs `offset` minutes after `time`.
def Bus.departsAfter (bus: Bus) (time: Nat): Bool := Nat.divides bus.id (time + bus.offset)

--| The times that suit some buses: `time`, and every `period` minutes after.
type Alignment = { time: Nat, period: Nat }

--| With no buses, every time suits.
def Alignment.start: Alignment := { time = 0, period = 1 }

--| The times that also suit `bus`: none if no time does. A bus with ID
--| `id` comes round to the same point in the period within `id` periods,
--| so both searches look no further.
def Alignment.add (alignment: Alignment) (bus: Bus): Option Alignment :=
  let suits := (periods: Nat) => bus.departsAfter (alignment.time + periods * alignment.period)
  0 ..< bus.id |> .find suits |> .map (first =>
    let again := 0 ..< bus.id |> .find (more => suits (first + 1 + more)) |> .getOrElse 0
    { time = alignment.time + first * alignment.period, period = (again + 1) * alignment.period })

def Alignment.addAll (alignment: Alignment): (buses: List Bus) → Option Alignment
  | [] => Some alignment
  | [bus, ..rest] => alignment.add bus |> .flatMap (next => next.addAll rest)

--| Part 2: the earliest time from which each bus departs its offset later;
--| none if there is no such time.
def Notes.earliestLineUp (notes: Notes): Option Nat := Alignment.start.addAll notes.buses |> .map (.time)
