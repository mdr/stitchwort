-- Advent of Code 2024, day 19: towel patterns, each a sequence of coloured
-- stripes, then the designs the onsen wants to display. A design is made by
-- laying towels end to end, any pattern any number of times, so that the
-- stripes match exactly. Part 1 counts the designs that can be made; part 2
-- adds up the number of different ways to make each one.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day19.main < examples/2024/day19.txt
--
-- The proofs are in `Aoc.Year2024.Day19.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day19.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day19
import Std (DecEq, Fail, IO, List, Nat, Parse, Text)
import Std.Parse (blankLine, lines, many1, pick, sepBy1, text)

def main(): {IO, Fail} () :=
  let onsen := parseOnsen IO.readAll()
  IO.print "Part 1: ${solvePart1 onsen}"
  IO.print "Part 2: ${solvePart2 onsen}"

type Stripe =
  | White
  | Blue
  | Black
  | Red
  | Green

-- A towel's stripes, in order.
def Pattern: Type := List Stripe

-- The stripes the onsen wants to display, in order.
def Design: Type := List Stripe

type Onsen = { patterns: List Pattern, designs: List Design }

def stripe(): {Parse} Stripe := pick [("w", White), ("u", Blue), ("b", Black), ("r", Red), ("g", Green)]

-- The patterns on one line, separated by commas, a blank line, then one
-- design per line.
def onsen(): {Parse} Onsen :=
  let patterns := sepBy1 (() => many1 stripe) (() => text ", ")
  blankLine()
  let designs := lines (() => many1 stripe)
  { patterns, designs }

def parseOnsen (input: Text): {Fail} Onsen := Parse.all input onsen

-- Whether `whole` begins with `start`.
def startsWith [auto decEq: DecEq a]: (whole: List a) → (start: List a) → Bool
  | whole, Nil => True
  | Nil, Cons first rest => False
  | Cons wholeFirst wholeRest, Cons first rest => wholeFirst == first && startsWith wholeRest rest

-- The number of ways to make each suffix of `design`, longest first: the
-- design itself, then without its first stripe, and so on down to the empty
-- suffix, made one way (with no towels). A suffix is made by a first towel
-- whose pattern it starts with, then the rest, which is a shorter suffix
-- whose count is already in the table. Every pattern has a stripe.
def waysForSuffixes (patterns: List Pattern): (design: Design) → List Nat
  | Nil => [1]
  | Cons first rest =>
    let later := waysForSuffixes patterns rest
    let ways := patterns.sumBy (pattern =>
      if startsWith (Cons first rest) pattern then later.getOr (pattern.length - 1) 0 else 0)
    Cons ways later

-- The number of different ways to make `design`.
def waysToMake (patterns: List Pattern) (design: Design): Nat := waysForSuffixes patterns design |> .headOr 0

def solvePart1 (onsen: Onsen): Nat := onsen.designs.count (design => waysToMake onsen.patterns design > 0)

def solvePart2 (onsen: Onsen): Nat := onsen.designs.sumBy (waysToMake onsen.patterns)
