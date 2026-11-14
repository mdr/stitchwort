--| Day 8 as the puzzle states it: a display's wiring connects each signal
--| wire to one segment, a pattern of wires shows a digit when the segments
--| its wires drive are exactly the digit's, and a wiring decodes a display
--| when its ten patterns show the ten digits. The answers read the output
--| through such a wiring. The proofs (Proofs/) show the program computes
--| them, for every input it reads.
--|
--| What the spec decides:
--|
--| - A wiring is any permutation of the segments: the segments the seven
--|   wires drive are the seven segments, each once (`IsWiring`).
--| - "The digit a pattern shows" is the first of 0 to 9 it shows (`shown`).
--|   Under a wiring at most one fits, since no two digits light the same
--|   segments, so "first" decides nothing.
--| - A display's answer uses a wiring that decodes it; the answer is the
--|   same whichever such wiring is used (`decodedValueUnique` in the
--|   proofs), so the puzzle's promise that there is exactly one isn't
--|   needed beyond there being one, and the parser checks that.

namespace Aoc.Year2021.Day08.Spec
import Aoc.Year2021.Day08 (Entry, Pattern, Segment, segments)
import Std (List, Nat, Option)

--| The segments each digit lights, as the puzzle draws them.
def digitSegments: Nat → List Segment
  | 0 => [A, B, C, E, F, G]
  | 1 => [C, F]
  | 2 => [A, C, D, E, G]
  | 3 => [A, C, D, F, G]
  | 4 => [B, C, D, F]
  | 5 => [A, B, D, F, G]
  | 6 => [A, B, D, E, F, G]
  | 7 => [A, C, F]
  | 8 => [A, B, C, D, E, F, G]
  | 9 => [A, B, C, D, F, G]
  | _ => []

--| The digits.
def digits: List Nat := List.range 0 10

--| `wiring wire` is the segment the wire drives. A wiring connects the
--| seven wires to the seven segments, one each.
def IsWiring (wiring: Segment → Segment): Prop := List.Perm (segments.map wiring) segments

--| Under the wiring, the pattern shows the digit: each wire is on exactly
--| when the segment it drives is one the digit lights.
def Shows (wiring: Segment → Segment) (pattern: Pattern) (digit: Nat): Bool :=
  segments.all (wire => pattern.has wire == (digitSegments digit).contains (wiring wire))

--| The digit the pattern shows under the wiring, if any.
def shown (wiring: Segment → Segment) (pattern: Pattern): Option Nat :=
  digits.find (digit => Shows wiring pattern digit)

--| The wiring decodes the display: it is a wiring, the ten patterns show the
--| ten digits (each once), and each output pattern shows a digit.
def Decodes (wiring: Segment → Segment) (entry: Entry): Prop :=
  IsWiring wiring
    ∧ List.Perm (entry.patterns.map (shown wiring)) (digits.map Some)
    ∧ entry.outputs.all (output => (shown wiring output).isSome) = True

--| The output value read through the wiring: its four digits in base 10.
def decodedValue (wiring: Segment → Segment) (entry: Entry): Nat :=
  entry.outputs.foldLeft 0 (n output => 10 * n + (shown wiring output).getOrElse 0)

--| Part 1 read through the wiring: the output digits that are 1, 4, 7 or 8.
def easyDigits (wiring: Segment → Segment) (entry: Entry): Nat :=
  entry.outputs.count (output => [Some 1, Some 4, Some 7, Some 8].contains (shown wiring output))

--| The answers: with `wiringOf entry` a wiring that decodes each entry, the
--| 1s, 4s, 7s and 8s in all the outputs (part 1), and the output values
--| added up (part 2).
def Part1Answer (entries: List Entry) (answer: Nat): Prop :=
  ∃ (wiringOf: Entry → Segment → Segment) => (∀ (entry: Entry) => entry ∈ entries → Decodes (wiringOf entry) entry)
    ∧ answer = entries.sumBy (entry => easyDigits (wiringOf entry) entry)

def Part2Answer (entries: List Entry) (answer: Nat): Prop :=
  ∃ (wiringOf: Entry → Segment → Segment) => (∀ (entry: Entry) => entry ∈ entries → Decodes (wiringOf entry) entry)
    ∧ answer = entries.sumBy (entry => decodedValue (wiringOf entry) entry)
