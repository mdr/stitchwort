--| Facts about the display as drawn, each checked by computing it, and the
--| small list lemmas the proofs use.

namespace Aoc.Year2021.Day08.Proofs
import Aoc.Year2021.Day08 (..)
import Aoc.Year2021.Day08.Spec (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Void)

--| How many digits light the segment.
def digitsLighting (segment: Segment): Nat := digits.count (digit => (digitSegments digit).contains segment)

--| A digit's score on the display as drawn, in the spec's terms.
def drawnScore (digit: Nat): Nat :=
  segments.sumBy (segment => if (digitSegments digit).contains segment then digitsLighting segment else 0)

--| A `Bool` fact about every digit holds of each.
theorem eachDigit ∀ (q: Nat → Bool) (all: digits.all q = True) (digit: Nat) (below: digit < 10): q digit = True :=
  List.allRangeElim q 10 0 all digit (Nat.zeroLe digit) below

--| Every segment is one of the seven.
theorem segmentsComplete ∀ (segment: Segment): segment ∈ segments := cases

--| The program's display is the spec's.
theorem displayDrawn ∀ (digit: Nat) (below: digit < 10) (segment: Segment):
    (digitPattern digit).has segment = (digitSegments digit).contains segment :=
  let q := (d: Nat) => segments.all (s => (digitPattern d).has s == (digitSegments d).contains s)
  let all: digits.all q = True := rfl
  let atDigit := eachDigit q all digit below
  (atDigit.read segment (segmentsComplete segment)).read

--| Each digit's drawn score reads as that digit.
theorem decodeDrawn ∀ (digit: Nat) (below: digit < 10): digitScores.indexOf (drawnScore digit) = digit :=
  let q := (d: Nat) => digitScores.indexOf (drawnScore d) == d
  let all: digits.all q = True := rfl
  DecEq.sound (eachDigit q all digit below)

--| Two digits that light the same segments are the same digit.
theorem digitsDiffer ∀ (first: Nat) (second: Nat) (firstBelow: first < 10) (secondBelow: second < 10)
    (same: segments.all (s => (digitSegments first).contains s == (digitSegments second).contains s) = True): first = second :=
  let r := (d: Nat) (e: Nat) => not (segments.all (s => (digitSegments d).contains s == (digitSegments e).contains s)) ∨ d == e
  let q := (d: Nat) => digits.all (e => r d e)
  let all: digits.all q = True := rfl
  let atFirst := eachDigit q all first firstBelow
  let atBoth := eachDigit (e => r first e) atFirst second secondBelow
  DecEq.sound (rewrite same at atBoth in atBoth)

--| The digits with 2, 3, 4 or 7 segments are 1, 7, 4 and 8.
theorem easyDrawn ∀ (digit: Nat) (below: digit < 10):
    [2, 3, 4, 7].contains (segments.count (s => (digitSegments digit).contains s)) = [Some 1, Some 4, Some 7, Some 8].contains (Some digit) :=
  let q := (d: Nat) =>
    [2, 3, 4, 7].contains (segments.count (s => (digitSegments d).contains s)) == [Some 1, Some 4, Some 7, Some 8].contains (Some d)
  let all: digits.all q = True := rfl
  DecEq.sound (eachDigit q all digit below)
