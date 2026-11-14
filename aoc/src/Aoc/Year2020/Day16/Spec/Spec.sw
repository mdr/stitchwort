--| Day 16 as the puzzle states it, about the notes' data (`Range`, `Rule`,
--| `Ticket`, `Notes`): how the notes are written, which values a field
--| allows, the scanning error rate (part 1), and what an order of the
--| fields is and the departure product under it (part 2). Nothing else is
--| shared with the program. The proofs (Proofs/) show the program computes
--| these.

namespace Aoc.Year2020.Day16.Spec
import Aoc.Year2020.Day16 (Notes, Range, Rule, Ticket)
import Std (Char, List, NonEmptyList, Parse, Text)

-- The format

def NumberWritten (read: List Char) (number: Nat): Prop :=
  read ≠ [] ∧ read.all Parse.isDigit = True ∧ number = Parse.digitsValue read

--| `1-3`: from 1 to 3.
def RangeWritten (read: List Char) (range: Range): Prop :=
  ∃ (lowRead: List Char) => ∃ (highRead: List Char) => read = lowRead ++ ['-'] ++ highRead
    ∧ NumberWritten lowRead range.low
    ∧ NumberWritten highRead range.high

--| "Rules for ticket fields specify a field's name and the valid ranges of
--| values for that field": `class: 1-3 or 5-7`. The name is any text
--| without a colon or a line break.
def RuleWritten (read: List Char) (rule: Rule): Prop :=
  ∃ (firstRead: List Char) => ∃ (secondRead: List Char) => read
    = rule.field.toList ++ ": ".toList ++ firstRead ++ " or ".toList ++ secondRead
    ∧ rule.field.toList ≠ []
    ∧ rule.field.toList.all (char => char != ':' && char != '\n') = True
    ∧ RangeWritten firstRead rule.first
    ∧ RangeWritten secondRead rule.second

--| "Each ticket is represented by a single line of comma-separated values."
def TicketWritten (read: List Char) (ticket: Ticket): Prop :=
  ∃ (values: NonEmptyList Nat) => Parse.SepBy NumberWritten (read u => read = [',']) read values
    ∧ ticket.values = values.toList

def LineBreakWritten (read: List Char) (u: ()): Prop := Parse.LineBreak read

--| The rules, one a line; a blank line, `your ticket:` and your ticket; a
--| blank line, `nearby tickets:` and the nearby tickets, one a line.
def NotesWritten (read: List Char) (notes: Notes): Prop :=
  ∃ (rulesRead: List Char) => ∃ (yoursRead: List Char) => ∃ (nearbyRead: List Char) => ∃ (blank1: List Char) =>
    ∃ (break1: List Char) => ∃ (blank2: List Char) => ∃ (break2: List Char) => read
      = rulesRead
        ++ blank1
        ++ "your ticket:".toList
        ++ break1
        ++ yoursRead
        ++ blank2
        ++ "nearby tickets:".toList
        ++ break2
        ++ nearbyRead
      ∧ (∃ (rules: NonEmptyList Rule) => Parse.SepBy RuleWritten LineBreakWritten rulesRead rules
        ∧ notes.rules = rules.toList)
      ∧ Parse.BlankLine blank1
      ∧ Parse.LineBreak break1
      ∧ TicketWritten yoursRead notes.yours
      ∧ Parse.BlankLine blank2
      ∧ Parse.LineBreak break2
      ∧ (∃ (nearby: NonEmptyList Ticket) => Parse.SepBy TicketWritten LineBreakWritten nearbyRead nearby
        ∧ notes.nearby = nearby.toList)

-- Part 1

--| "The ranges for each field ... are inclusive."
def inRange (range: Range) (value: Nat): Bool := range.low <= value && value <= range.high

--| "class: 1-3 or 5-7" means "valid ranges of 1-3 or 5-7 (inclusive)".
def validFor (rule: Rule) (value: Nat): Bool := inRange rule.first value || inRange rule.second value

def validForSomeField (rules: List Rule) (value: Nat): Bool := rules.any (rule => validFor rule value)

--| "Start by determining which tickets are completely invalid; these are
--| tickets that contain values which aren't valid for any field. ... Adding
--| together all of the invalid values produces your ticket scanning error
--| rate." Your ticket isn't scanned: "consider the validity of the nearby
--| tickets you scanned".
def errorRate (notes: Notes): Nat :=
  notes.nearby.sumBy (ticket => ticket.values.sumBy (value => if validForSomeField notes.rules value then 0 else value))

def Part1 (notes: Notes) (answer: Nat): Prop := answer = errorRate notes

-- Part 2

--| "Now that you've identified which tickets contain invalid values,
--| discard those tickets entirely. Use the remaining valid tickets to
--| determine which field is which."
def ValidTicket (rules: List Rule) (ticket: Ticket): Prop := ticket.values.all (validForSomeField rules) = True

--| "Determine what order the fields appear on the tickets. The order is
--| consistent between all tickets: if seat is the third field, it is the
--| third field on every ticket": `order` gives the field at each position.
--| There are as many positions as fields, each position's field is one of
--| the rules, and no field is at two positions, so each field is at exactly
--| one. On every valid nearby ticket, each value is valid for the field at
--| its position.
def FieldOrder (notes: Notes) (order: List Rule): Prop :=
  order.length = notes.rules.length
    ∧ order.Distinct
    ∧ (∀ (rule: Rule) => rule ∈ order → rule ∈ notes.rules)
    ∧ (∀ (ticket: Ticket) => ticket ∈ notes.nearby
      → ValidTicket notes.rules ticket
      → List.All2 (rule value => validFor rule value = True) order ticket.values)

--| "Look for the six fields on your ticket that start with the word
--| departure. What do you get if you multiply those six values together?":
--| the product of the values whose field, in `order`, starts with
--| `departure`.
def departureProduct: (order: List Rule) → (values: List Nat) → Nat
  | [rule, ..order], [value, ..values] =>
    (if rule.field.startsWith "departure" then value else 1) * departureProduct order values
  | _, _ => 1

--| The answer is the departure product under an order of the fields.
--| Whether only one order fits depends on the notes (two fields with the
--| same ranges could swap); the proofs show that when the program's
--| elimination settles every position, its order is the only one.
def Part2 (notes: Notes) (answer: Nat): Prop :=
  ∃ (order: List Rule) => FieldOrder notes order ∧ answer = departureProduct order notes.yours.values
