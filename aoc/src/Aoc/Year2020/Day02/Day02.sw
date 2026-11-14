--| Advent of Code 2020, day 2: a password database, one entry per line, each a
--| policy and a password, as in `1-3 a: abcde`. Part 1 reads the policy as the
--| fewest and most times the letter may appear; part 2 as two positions,
--| counting from 1, exactly one of which must hold the letter. Each part
--| counts the passwords that keep their policy.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day02.main < inputs/2020/day02.txt
--|
--| The puzzle input is committed in aoc/inputs/2020/. The proofs, that the
--| parser reads exactly the puzzle's format and that both checks are the
--| puzzle's, are in `Aoc.Year2020.Day02.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2020.Day02.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2020.Day02
import Std (Char, Fail, IO, List, Parse, Text)
import Std.Parse (char, nat, satisfy, takeWhile1, text)

def main(): {IO, Fail} () :=
  let entries := parseEntries IO.readAll()
  IO.print "Part 1: ${solvePart1 entries}"
  IO.print "Part 2: ${solvePart2 entries}"

--| A line of the database: the policy's two numbers and letter, and the
--| password.
type Entry = { low: Nat, high: Nat, letter: Char, password: Text }

--| `1-3 a: abcde`: two numbers with a dash between them, a space, a
--| lowercase letter, a colon and a space, and a password of lowercase letters.
def line(): {Parse} Entry :=
  let low := nat()
  char '-'
  let high := nat()
  char ' '
  let letter := satisfy "a lowercase letter" Char.isAsciiLowercase
  text ": "
  let password := takeWhile1 "a password" Char.isAsciiLowercase
  { low, high, letter, password }

--| One entry per line. Anything else fails, naming the line and column.
def parseEntries (input: Text): {Fail} List Entry := Parse.eachLine input line

--| Part 1's policy: the letter appears from `low` to `high` times.
def Entry.validByCount (entry: Entry): Bool :=
  let times := entry.password.toList.count (== entry.letter)
  entry.low <= times <= entry.high

--| Whether the letter is at `position` of the password, counting from 1:
--| there is no position 0.
def Entry.letterAt (entry: Entry) (position: Nat): Bool := match position with
  | Zero => False
  | Succ index => entry.password.toList.get index == Some entry.letter

--| Part 2's policy: the letter is at exactly one of `low` and `high`.
def Entry.validByPosition (entry: Entry): Bool := entry.letterAt entry.low != entry.letterAt entry.high

def solvePart1 (entries: List Entry): Nat := entries.count Entry.validByCount

def solvePart2 (entries: List Entry): Nat := entries.count Entry.validByPosition
