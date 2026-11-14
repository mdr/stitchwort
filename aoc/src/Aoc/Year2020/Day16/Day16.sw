--| Advent of Code 2020, day 16: ticket translation. The notes give a rule
--| for each field of a ticket (`departure location: 45-422 or 444-950`: its
--| values lie in one of two inclusive ranges), then your ticket, then the
--| nearby tickets, each a line of values separated by commas. The values
--| are in the same order on every ticket, but which field is which isn't
--| said. Part 1 is the ticket scanning error rate: the sum of the nearby
--| tickets' values that are valid for no field. Part 2 drops the tickets
--| with such a value, works out which position is which field, and
--| multiplies the six values on your ticket whose field starts with
--| `departure`.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day16.main < inputs/2020/day16.txt
--|
--| Part 2 first rules out, at each position, every field that some valid
--| ticket's value there doesn't fit; then `Aoc.Common.assign` over and over
--| settles a position with one field left, a field no other position can
--| then have.
--| The proofs, that the parser reads the puzzle's format, that part 1 is
--| the puzzle's sum, and that part 2's order of the fields is one the
--| puzzle allows and the only one, are in `Aoc.Year2020.Day16.Proofs`
--| (Proofs/), and the tests in `Aoc.Year2020.Day16.Tests` (Tests/); `run`
--| checks neither.

namespace Aoc.Year2020.Day16
import Aoc.Common (assign)
import Std (Fail, IO, List, NonEmptyList, Option, Parse, Text)

def main(): {IO, Fail} () :=
  let notes := parseNotes IO.readAll()
  IO.print "Part 1: ${notes.errorRate}"
  match notes.departureProduct with
    | Some product => IO.print "Part 2: ${product}"
    | None => Fail.fail "the tickets don't settle which field is which"

--| The values from `low` to `high`, both included.
type Range = { low: Nat, high: Nat }

def Range.contains (range: Range) (value: Nat): Bool := range.low <= value && value <= range.high

type Rule = { field: Text, first: Range, second: Range }

def Rule.allows (rule: Rule) (value: Nat): Bool := rule.first.contains value || rule.second.contains value

def Rule.isDeparture (rule: Rule): Bool := rule.field.startsWith "departure"

--| A ticket's values, in the order of the fields (the same on every ticket).
type Ticket = { values: List Nat }

type Notes = { rules: List Rule, yours: Ticket, nearby: List Ticket }

-- The format

def range(): {Parse} Range :=
  let low := Parse.nat()
  Parse.char '-'
  let high := Parse.nat()
  { low, high }

def isNameChar (char: Char): Bool := char != ':' && char != '\n'

def rule(): {Parse} Rule :=
  let field := Parse.takeWhile1 "a field name" isNameChar
  Parse.text ": "
  let first := range()
  Parse.text " or "
  let second := range()
  { field, first, second }

def ticket(): {Parse} Ticket :=
  let values := Parse.sepBy1 Parse.nat (() => Parse.char ',')
  { values = values.toList }

def notes(): {Parse} Notes :=
  let rules := Parse.lines rule
  Parse.blankLine()
  Parse.text "your ticket:"
  Parse.newline()
  let yours := ticket()
  Parse.blankLine()
  Parse.text "nearby tickets:"
  Parse.newline()
  let nearby := Parse.lines ticket
  { rules = rules.toList, yours, nearby = nearby.toList }

def parseNotes (input: Text): {Fail} Notes := Parse.all input notes

-- Part 1

def Notes.fitsSomeField (notes: Notes) (value: Nat): Bool := notes.rules.any (rule => rule.allows value)

--| Part 1: the sum of the nearby tickets' values that fit no field.
def Notes.errorRate (notes: Notes): Nat :=
  notes.nearby.flatMap .values |> .filter (value => not (notes.fitsSomeField value)) |> .sum

-- Part 2

def Notes.isValid (notes: Notes) (ticket: Ticket): Bool := ticket.values.all notes.fitsSomeField

def Notes.validTickets (notes: Notes): List Ticket := notes.nearby.filter notes.isValid

def allowing (fields: List Rule) (value: Nat): List Rule := fields.filter (rule => rule.allows value)

--| The fields still possible at each position, once `ticket` has ruled out
--| those that don't allow its value there.
def narrow (candidates: List (List Rule)) (ticket: Ticket): List (List Rule) :=
  List.zipWith candidates ticket.values allowing

--| For each position, the fields that allow every valid ticket's value there.
def Notes.candidates (notes: Notes): List (List Rule) :=
  notes.validTickets.foldLeft (List.replicate notes.rules.length notes.rules) narrow

--| The field at each position, if the tickets settle it. Every valid
--| ticket must have a value for every field.
def Notes.fieldOrder (notes: Notes): Option (List Rule) :=
  if notes.validTickets.all (ticket => ticket.values.length == notes.rules.length) then assign notes.candidates
  else None

--| The product of the ticket's values whose field, in `order`, starts with
--| `departure`.
def Ticket.departureProduct (ticket: Ticket) (order: List Rule): Nat :=
  List.zip order ticket.values |> .filter (pair => pair.fst.isDeparture) |> .map .snd |> .product

--| Part 2: your ticket's departure product, if the fields settle.
def Notes.departureProduct (notes: Notes): Option Nat := notes.fieldOrder.map notes.yours.departureProduct
