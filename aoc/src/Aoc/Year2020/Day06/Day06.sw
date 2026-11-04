--| Advent of Code 2020, day 6: customs declaration forms. Each person
--| answers the questions `a` to `z` and writes the letters of those they
--| answered "yes" to on a line; the people travelling together are a group,
--| with a blank line between groups. Part 1 sums, over the groups, the
--| number of questions anyone in the group answered "yes" to; part 2 the
--| number everyone in the group did.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day06.main < inputs/2020/day06.txt
--|
--| The program keeps each person's answers as a set of letters, and a
--| group's as their union (part 1) or intersection (part 2). The proofs,
--| that the parser reads the puzzle's format and that both sums are the
--| puzzle's counts of questions, are in `Aoc.Year2020.Day06.Proofs`
--| (Proofs/), and the tests in `Aoc.Year2020.Day06.Tests` (Tests/); `run`
--| checks neither.

namespace Aoc.Year2020.Day06
import Std (Char, Fail, IO, List, Nat, Parse, Set, Text)

def main(): {IO, Fail} () :=
  let groups := parseGroups IO.readAll()
  IO.print "Part 1: ${solvePart1 groups}"
  IO.print "Part 2: ${solvePart2 groups}"

--| The questions: `a` to `z`.
def questions: List Char := "abcdefghijklmnopqrstuvwxyz".toList

def isQuestion (char: Char): Bool := questions.contains char

--| The questions one person answered "yes" to.
type Person = { answers: Set Char }

--| One person's line: the letters of their "yes" answers.
def person(): {Parse} Person :=
  let letters := Parse.many1 (() => Parse.satisfy "a question, 'a' to 'z'" isQuestion)
  { answers = Set.fromList letters }

--| The people travelling together, a line each.
type Group = { people: List Person }

def group(): {Parse} Group := { people = Parse.lines person }

def parseGroups (input: Text): {Fail} List Group := Parse.all input (() => Parse.sections group)

--| The questions anyone in the group answered "yes" to.
def Group.anyone (group: Group): Set Char := Set.unions (group.people.map (.answers))

--| The questions everyone in the group answered "yes" to.
def Group.everyone (group: Group): Set Char :=
  group.people.foldLeft (Set.fromList questions) (common person => common.intersect person.answers)

def solvePart1 (groups: List Group): Nat := groups.sumBy (group => group.anyone.size)

def solvePart2 (groups: List Group): Nat := groups.sumBy (group => group.everyone.size)
