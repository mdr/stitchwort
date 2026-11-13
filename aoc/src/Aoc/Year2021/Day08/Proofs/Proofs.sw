--| Day 8 proved: for every wiring that decodes a display (Spec/), the
--| program reads its output value, and counts its 1s, 4s, 7s and 8s, as
--| the wiring does. With the parser's check (Parse.sw), the answers hold
--| of every input `parseEntries` reads, with no hypothesis.
-- The reason: renaming the wires changes no pattern's score, so a
-- pattern's score is that of the digit it shows on the display as drawn
-- (`scoreDrawn`), and those scores tell the digits apart (`decodeDrawn`).

namespace Aoc.Year2021.Day08.Proofs
import Aoc.Year2021.Day08 (..)
import Aoc.Year2021.Day08.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, List, Nat, Option, Void)

--| The answers, for any choice of a decoding wiring for each entry.

theorem part1Correct (entries: List Entry) (wiringOf: Entry → Segment → Segment)
    (decodes: ∀ (entry: Entry) => entry ∈ entries → Decodes (wiringOf entry) entry):
    solvePart1 entries = entries.sumBy (entry => easyDigits (wiringOf entry) entry) :=
  List.sumByCongMem entries _ _ (entry m => easyCorrect (wiringOf entry) entry (decodes entry m))

theorem part2Correct (entries: List Entry) (wiringOf: Entry → Segment → Segment)
    (decodes: ∀ (entry: Entry) => entry ∈ entries → Decodes (wiringOf entry) entry):
    solvePart2 entries = entries.sumBy (entry => decodedValue (wiringOf entry) entry) :=
  List.sumByCongMem entries _ _ (entry m => valueCorrect (wiringOf entry) entry (decodes entry m))

--| The spec's answers name one number each, whichever wirings are chosen.
theorem part1AnswerUnique (entries: List Entry) (first: Nat) (second: Nat) (h1: Part1Answer entries first) (h2: Part1Answer entries second):
    first = second :=
  match h1, h2 with
    | Witness w1 (Both d1 e1), Witness w2 (Both d2 e2) =>
      Eq.trans e1 (Eq.trans (Eq.sym (part1Correct entries w1 d1)) (Eq.trans (part1Correct entries w2 d2) (Eq.sym e2)))

theorem part2AnswerUnique (entries: List Entry) (first: Nat) (second: Nat) (h1: Part2Answer entries first) (h2: Part2Answer entries second):
    first = second :=
  match h1, h2 with
    | Witness w1 (Both d1 e1), Witness w2 (Both d2 e2) =>
      Eq.trans e1 (Eq.trans (Eq.sym (part2Correct entries w1 d1)) (Eq.trans (part2Correct entries w2 d2) (Eq.sym e2)))

--| Two wirings that decode a display read the same output value.
theorem decodedValueUnique (first: Segment → Segment) (second: Segment → Segment) (entry: Entry)
    (d1: Decodes first entry) (d2: Decodes second entry): decodedValue first entry = decodedValue second entry :=
  Eq.trans (Eq.sym (valueCorrect first entry d1)) (valueCorrect second entry d2)

-- One display.

--| The program's output value is the one the wiring reads.
theorem valueCorrect (wiring: Segment → Segment) (entry: Entry) (decodes: Decodes wiring entry):
    entry.value = decodedValue wiring entry :=
  match decodes with
    | Both wired (Both perm outputs) =>
      List.foldLeftCongMem entry.outputs 0 _ _ (n output m =>
        match e: shown wiring output with
          | None => Void.exfalso (notNone (shown wiring output) (outputs.read output m) e)
          | Some digit => Eq.cong (k => 10 * n + k) (decodeShown wiring entry decodes output digit e))

--| The program's count of 1s, 4s, 7s and 8s is the one the wiring reads.
theorem easyCorrect (wiring: Segment → Segment) (entry: Entry) (decodes: Decodes wiring entry):
    entry.outputs.count (output => [2, 3, 4, 7].contains output.size) = easyDigits wiring entry :=
  match decodes with
    | Both wired (Both perm outputs) =>
      List.countCongMem _ _ _ (output m =>
        match e: shown wiring output with
          | None => Void.exfalso (notNone (shown wiring output) (outputs.read output m) e)
          | Some digit =>
            match List.findRangeSome (d => Shows wiring output d) 10 digit e with
              | Both shows (Both below _) => Eq.trans (Eq.cong (k => [2, 3, 4, 7].contains k) (sizeDrawn wiring wired output digit shows)) (easyDrawn digit below))

--| A pattern that shows a digit reads as it.
theorem decodeShown (wiring: Segment → Segment) (entry: Entry) (decodes: Decodes wiring entry) (pattern: Pattern) (digit: Nat)
    (h: shown wiring pattern = Some digit): decodeDigit entry.patterns pattern = digit :=
  match List.findRangeSome (d => Shows wiring pattern d) 10 digit h with
    | Both shows (Both below _) =>
      Eq.trans (Eq.cong (s => digitScores.indexOf s) (scoreDrawn wiring entry decodes pattern digit shows)) (decodeDrawn digit below)

--| A pattern's score is the score of the digit it shows, on the display as
--| drawn.
theorem scoreDrawn (wiring: Segment → Segment) (entry: Entry) (decodes: Decodes wiring entry) (pattern: Pattern) (digit: Nat)
    (shows: Shows wiring pattern digit = True): score entry.patterns pattern = drawnScore digit :=
  match decodes with
    | Both wired rest =>
      let lit := (segment: Segment) => if (digitSegments digit).contains segment then digitsLighting segment else 0
      calc score entry.patterns pattern
        _ = segments.sumBy (wire => if pattern.has wire then litIn entry.patterns wire else 0)
        _ = segments.sumBy (wire => lit (wiring wire))
          := List.sumByCong segments _ _ (wire =>
            rewrite hasDrawn wiring pattern digit shows wire, litDrawn wiring entry decodes wire in rfl)
        _ = drawnScore digit := sumRewired wiring wired lit

--| How many patterns have a wire on is how many digits light the segment it
--| drives.
theorem litDrawn (wiring: Segment → Segment) (entry: Entry) (decodes: Decodes wiring entry) (wire: Segment):
    litIn entry.patterns wire = digitsLighting (wiring wire) :=
  match decodes with
    | Both wired (Both perm outputs) =>
      let lights := (o: Option Nat) => Option.fold o False (d => (digitSegments d).contains (wiring wire))
      calc litIn entry.patterns wire
        _ = entry.patterns.count (pattern => pattern.has wire)
        _ = entry.patterns.count (pattern => lights (shown wiring pattern))
          := List.countCongMem _ _ _ (pattern m =>
            let listed := List.memPerm (entry.patterns.map (shown wiring)) (digits.map Some) perm (shown wiring pattern) (List.memMap entry.patterns pattern m (shown wiring))
            match List.memMapElim Some (shown wiring pattern) digits listed with
              | Witness digit (Both _ isShown) =>
                match List.findRangeSome (d => Shows wiring pattern d) 10 digit (Eq.sym isShown) with
                  | Both shows _ => rewrite <- isShown, hasDrawn wiring pattern digit shows wire in rfl)
        _ = (entry.patterns.map (shown wiring)).count lights := Eq.sym (List.countMap entry.patterns lights (shown wiring))
        _ = (digits.map Some).count lights := List.countPerm (entry.patterns.map (shown wiring)) (digits.map Some) perm lights
        _ = digitsLighting (wiring wire) := List.countMap digits lights Some

--| A pattern's size is the number of segments of the digit it shows.
theorem sizeDrawn (wiring: Segment → Segment) (wired: IsWiring wiring) (pattern: Pattern) (digit: Nat)
    (shows: Shows wiring pattern digit = True): pattern.size = segments.count (s => (digitSegments digit).contains s) :=
  calc pattern.size
    _ = segments.count (wire => pattern.has wire)
    _ = segments.count (wire => (digitSegments digit).contains (wiring wire))
      := List.countCongMem _ _ _ (wire _ => hasDrawn wiring pattern digit shows wire)
    _ = segments.count (s => (digitSegments digit).contains s) := countRewired wiring wired (s => (digitSegments digit).contains s)

--| What `Shows` says of one wire.
theorem hasDrawn (wiring: Segment → Segment) (pattern: Pattern) (digit: Nat) (shows: Shows wiring pattern digit = True) (wire: Segment):
    pattern.has wire = (digitSegments digit).contains (wiring wire) :=
  (shows.read wire (segmentsComplete wire)).read

-- Renaming the wires.

--| A count over the wires is the count over the segments they drive.
theorem countRewired (wiring: Segment → Segment) (wired: IsWiring wiring) (h: Segment → Bool):
    segments.count (wire => h (wiring wire)) = segments.count h :=
  Eq.trans (Eq.sym (List.countMap segments h wiring)) (List.countPerm (segments.map wiring) segments wired h)

theorem sumRewired (wiring: Segment → Segment) (wired: IsWiring wiring) (h: Segment → Nat):
    segments.sumBy (wire => h (wiring wire)) = segments.sumBy h :=
  Eq.trans (Eq.sym (List.sumByMap segments h wiring)) (List.sumByPerm (segments.map wiring) segments wired h)

theorem allRewired (wiring: Segment → Segment) (wired: IsWiring wiring) (h: Segment → Bool):
    segments.all (wire => h (wiring wire)) = segments.all h :=
  Eq.trans (Eq.sym (List.allMapBool segments h wiring)) (List.allPerm (segments.map wiring) segments wired h)

--| Under a wiring, a pattern shows at most one digit, so it shows the digit
--| `shown` finds.
theorem shownOf (wiring: Segment → Segment) (wired: IsWiring wiring) (pattern: Pattern) (digit: Nat) (below: digit < 10)
    (shows: Shows wiring pattern digit = True): shown wiring pattern = Some digit :=
  let passes := (d: Nat) => Shows wiring pattern d
  match e: digits.find passes with
    | None => Void.exfalso (List.findNoneNotMem digits passes digit shows (List.memRangeFromIntro digit 10 0 (Nat.zeroLe digit) below) e)
    | Some found =>
      match List.findRangeSome passes 10 found e with
        | Both foundShows (Both foundBelow _) => Eq.cong Some (sameDigit wiring wired pattern found digit foundBelow below foundShows shows)

theorem sameDigit (wiring: Segment → Segment) (wired: IsWiring wiring) (pattern: Pattern) (first: Nat) (second: Nat)
    (firstBelow: first < 10) (secondBelow: second < 10) (firstShows: Shows wiring pattern first = True) (secondShows: Shows wiring pattern second = True):
    first = second :=
  let agree := (s: Segment) => (digitSegments first).contains s == (digitSegments second).contains s
  let atWires: segments.all (wire => agree (wiring wire)) = True :=
    List.allTrue segments _ (wire =>
      rewrite <- hasDrawn wiring pattern first firstShows wire, <- hasDrawn wiring pattern second secondShows wire in boolEqSelf (pattern.has wire))
  digitsDiffer first second firstBelow secondBelow (rewrite <- allRewired wiring wired agree in atWires)

theorem boolEqSelf (b: Bool): (b == b) = True := cases

theorem notNone (o: Option a) (some: o.isSome = True) (none: o = None): Void := rewrite none at some in Bool.falseNotTrue some
