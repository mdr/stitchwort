--| Day 16's puzzle examples, the parser, and the elimination on its own.

namespace Aoc.Year2020.Day16.Tests
import Aoc.Year2020.Day16 (..)
import Std (Fail, List, Option, Result, Text)

def parsed (input: Text): Result Notes Text := Fail.toResult (() => parseNotes input)

def errorRate (input: Text): Result Nat Text := (parsed input).map (.errorRate)

def fieldNames (input: Text): Result (Option (List Text)) Text :=
  (parsed input).map (notes => notes.fieldOrder.map (order => order.map (.field)))

--| Part 1's example: three of the four nearby tickets have a value no
--| field allows (4, 55 and 12).
def example: Text := """
  class: 1-3 or 5-7
  row: 6-11 or 33-44
  seat: 13-40 or 45-50

  your ticket:
  7,1,14

  nearby tickets:
  7,3,47
  40,4,50
  55,2,20
  38,6,12
  """

--| Part 2's example, where every ticket is valid.
def example2: Text := """
  class: 0-1 or 4-19
  row: 0-5 or 8-19
  seat: 0-13 or 16-19

  your ticket:
  11,12,13

  nearby tickets:
  3,9,18
  15,1,5
  5,14,9
  """

test "the example's notes" :=
  (parsed example).map (notes => (notes.rules.map (.field), notes.yours.values, notes.nearby.map (.values)))
    == Ok (["class", "row", "seat"], [7, 1, 14], [[7, 3, 47], [40, 4, 50], [55, 2, 20], [38, 6, 12]])

test "the example's second rule" :=
  (parsed example).map (notes => notes.rules.get 1)
    == Ok (Some { field = "row", first = { low = 6, high = 11 }, second = { low = 33, high = 44 } })

test "the example, part 1" := errorRate example == Ok 71
test "the example, one valid ticket" :=
  (parsed example).map (notes => notes.validTickets.map (.values)) == Ok [[7, 3, 47]]

test "the example 2, part 1" := errorRate example2 == Ok 0
test "the example 2's order: row, class, seat" := fieldNames example2 == Ok (Some ["row", "class", "seat"])
test "the example's order: row, class, seat" := fieldNames example == Ok (Some ["row", "class", "seat"])
test "no departure fields multiply to 1" := (parsed example2).map (.departureProduct) == Ok (Some 1)

test "the example 2's candidates" :=
  (parsed example2).map (notes => notes.candidates.map (fields => fields.map (.field)))
    == Ok [["row"], ["class", "row"], ["class", "row", "seat"]]

test "range ends are included" := ({ low = 3, high = 5 }: Range).contains 3 && ({ low = 3, high = 5 }: Range).contains 5
test "a departure field" :=
  ({ field = "departure time", first = { low = 0, high = 1 }, second = { low = 2, high = 3 } }: Rule).isDeparture

test "two fields that fit everywhere don't settle" :=
  fieldNames "a: 0-9 or 10-19\nb: 0-9 or 10-19\n\nyour ticket:\n1,2\n\nnearby tickets:\n3,4" == Ok None
test "a ticket with too few values doesn't settle" :=
  fieldNames "a: 0-1 or 2-3\nb: 4-5 or 6-7\n\nyour ticket:\n1,4\n\nnearby tickets:\n1" == Ok None
test "the departure product" :=
  (parsed
      "departure a: 0-1 or 2-3\nb: 4-5 or 6-7\ndeparture c: 8-9 or 10-11\n\nyour ticket:\n4,10,3\n\nnearby tickets:\n5,9,1").map
    (.departureProduct)
    == Ok (Some 30)

test "the notes need your ticket" := not (parsed "a: 0-1 or 2-3\n\nnearby tickets:\n1").isOk
test "a rule has two ranges" := not (parsed "a: 0-1\n\nyour ticket:\n1\n\nnearby tickets:\n1").isOk
