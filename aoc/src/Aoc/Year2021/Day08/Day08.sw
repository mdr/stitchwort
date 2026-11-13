--| Advent of Code 2021, day 8: a seven-segment display whose wires are mixed
--| up. A digit lights some of the segments a to g; each signal wire drives
--| one segment, but which one is scrambled, differently on each display.
--| Each line of the input is one display: the ten patterns of wires that its
--| ten digits light, in no order, then `|` and the four patterns of its
--| output value. Part 1 counts the output digits that are 1, 4, 7 or 8 (the
--| digits with a number of segments no other digit has); part 2 works out
--| each display's wiring, reads its four-digit output and adds them up.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day08.main < inputs/2021/day08.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| The program reads a digit by a score that doesn't depend on the wiring:
--| for each wire a pattern lights, the number of the ten patterns that light
--| it, added up. Each digit has a score no other has (the display's own
--| digits give 42 for 0, 17 for 1, and so on), and renaming the wires
--| changes no score, so a pattern's score names its digit. The parser also
--| works out each display's wiring from the digits read, and fails unless it
--| shows the ten digits, so the answers' theorems need no hypothesis. The
--| proofs are in `Aoc.Year2021.Day08.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2021.Day08.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day08
import Std (Fail, IO, List, Nat, Parse, Text)
import Std.Parse (char, takeWhile1, text)

def main(): {IO, Fail} () :=
  let entries := parseEntries IO.readAll()
  IO.print "Part 1: ${solvePart1 entries}"
  IO.print "Part 2: ${solvePart2 entries}"

--| A segment of the display, or a signal wire, by its letter.
type Segment = | A | B | C | D | E | F | G

def segments: List Segment := [A, B, C, D, E, F, G]

--| A pattern: which wires (or segments) are on.
type Pattern = { a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, f: Bool, g: Bool }

def Pattern.has (pattern: Pattern): Segment → Bool
  | A => pattern.a
  | B => pattern.b
  | C => pattern.c
  | D => pattern.d
  | E => pattern.e
  | F => pattern.f
  | G => pattern.g

--| The number of wires on.
def Pattern.size (pattern: Pattern): Nat := segments.count pattern.has

def Pattern.ofLetters (letters: Text): Pattern :=
  let chars := letters.toList
  {
    a = chars.contains 'a',
    b = chars.contains 'b',
    c = chars.contains 'c',
    d = chars.contains 'd',
    e = chars.contains 'e',
    f = chars.contains 'f',
    g = chars.contains 'g'
  }

--| One display: its ten digits' patterns, and its output's.
type Entry = { patterns: List Pattern, outputs: List Pattern }

--| The segments each digit lights, 0 to 9, on a display wired as drawn.
def display: List Pattern :=
  ["abcefg", "cf", "acdeg", "acdfg", "bcdf", "abdfg", "abdefg", "acf", "abcdefg", "abcdfg"].map Pattern.ofLetters

def digitPattern (digit: Nat): Pattern := display.getOr digit (Pattern.ofLetters "")

--| How many of the patterns have wire `wire` on.
def litIn (patterns: List Pattern) (wire: Segment): Nat := patterns.count (.has wire)

--| The pattern's score among `patterns`: for each wire it has on, how many
--| of `patterns` have it on, added up.
def score (patterns: List Pattern) (pattern: Pattern): Nat :=
  segments.sumBy (wire => if pattern.has wire then litIn patterns wire else 0)

--| Each digit's score on the display as drawn.
def digitScores: List Nat := display.map (score display)

--| The digit with the pattern's score (10 if none has it).
def decodeDigit (patterns: List Pattern) (pattern: Pattern): Nat := digitScores.indexOf (score patterns pattern)

--| The output value: its digits, read in base 10.
def Entry.value (entry: Entry): Nat := entry.outputs.foldLeft 0 (n output => 10 * n + decodeDigit entry.patterns output)

--| Part 1: the output digits with 2, 3, 4 or 7 segments on, which are the
--| 1s, 7s, 4s and 8s.
def solvePart1 (entries: List Entry): Nat :=
  entries.sumBy (entry => entry.outputs.count (output => [2, 3, 4, 7].contains output.size))

--| Part 2: the output values added up.
def solvePart2 (entries: List Entry): Nat := entries.sumBy Entry.value

--| A wiring, as the segment each wire drives.
type Wiring = { a: Segment, b: Segment, c: Segment, d: Segment, e: Segment, f: Segment, g: Segment }

def Wiring.at (wiring: Wiring): Segment → Segment
  | A => wiring.a
  | B => wiring.b
  | C => wiring.c
  | D => wiring.d
  | E => wiring.e
  | F => wiring.f
  | G => wiring.g

--| The wiring the digits read give: wire `x` drives the segment that is on
--| in the digits of exactly the patterns that have `x` on (`A` if none
--| is).
-- Opaque: the proofs need only its name, since `Entry.wired` checks what
-- they use of it, and on an unknown entry its body is a large term that
-- checking `parseEntries`' proofs would otherwise compute.
opaque def Entry.wiring (entry: Entry): Wiring :=
  let read := entry.patterns.map (pattern => (pattern, digitPattern (decodeDigit entry.patterns pattern)))
  let drives := (wire: Segment) =>
    segments.find (segment => read.all (((pattern, digit)) => pattern.has wire == digit.has segment)) |> .getOrElse A
  { a = drives A, b = drives B, c = drives C, d = drives D, e = drives E, f = drives F, g = drives G }

--| Under the wiring, the pattern shows the digit read from it.
def showsRead (wiring: Wiring) (patterns: List Pattern) (pattern: Pattern): Bool :=
  let digit := decodeDigit patterns pattern
  digit < 10 ∧ segments.all (wire => pattern.has wire == (digitPattern digit).has (wiring.at wire))

--| The entry's wiring sends the seven wires to the seven segments, the ten
--| patterns read as the ten digits, and every pattern, output too, shows
--| the digit read from it.
def Entry.wired (entry: Entry): Bool :=
  let wiring := entry.wiring
  segments.map wiring.at |> .sort == segments
    ∧ entry.patterns.map (decodeDigit entry.patterns) |> .sort == List.range 0 10
    ∧ entry.patterns ++ entry.outputs |> .all (showsRead wiring entry.patterns)

--| One display, `p1 … p10 | o1 o2 o3 o4`, each pattern its wires' letters.
def Entry.parse(): {Parse} Entry :=
  let patterns := Parse.exactly 10 (() =>
    let pattern := patternParse()
    char ' '
    pattern)
  text "| "
  let outputs := Parse.exactly 4 (() =>
    let pattern := patternParse()
    Parse.optional (() => char ' ')
    pattern)
  { patterns, outputs }

def patternParse(): {Parse} Pattern := takeWhile1 "a letter from a to g" (c => 'a' ≤ c ≤ 'g') |> Pattern.ofLetters

--| One display per line. A display whose digits don't give a wiring that
--| shows them fails, naming it.
def parseEntries (input: Text): {Fail} List Entry := checkWired (Parse.eachLine input Entry.parse)

def checkWired (entries: List Entry): {Fail} List Entry := match firstUnwired entries with
  | Some (index, _) => Fail.fail "line ${index + 1}: no wiring found that shows the ten digits"
  | None => entries

--| The first entry, with its index, whose wiring doesn't check.
def firstUnwired (entries: List Entry): Option (Nat, Entry) :=
  entries.withIndex.find (((_, entry)) => not entry.wired)
