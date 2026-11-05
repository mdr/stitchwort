--| Day 6 as the puzzle states it, on the groups as the lines their people
--| wrote. The proofs (Proofs/) show the program's sums are these.

namespace Aoc.Year2020.Day06.Spec
import Std (Bool, Char, List, Nat, Text)

--| "The form asks a series of 26 yes-or-no questions marked a through z."
def questions: List Char := "abcdefghijklmnopqrstuvwxyz".toList

--| One line per person in the group: the questions they answered "yes" to.
--| "For each of the people in the group", `anyone` answered "yes" to a
--| question when some line has its letter.
def anyone (group: List (List Char)) (question: Char): Bool := group.any (line => line.contains question)

--| `everyone` answered "yes" to a question when every line has its letter.
def everyone (group: List (List Char)) (question: Char): Bool := group.all (line => line.contains question)

--| "Count the number of questions to which" `yes` holds, for one group.
def count (yes: List (List Char) → Char → Bool) (group: List (List Char)): Nat := (questions.filter (yes group)).length

--| "Groups are separated by blank lines": a line with nothing but spaces
--| and tabs. The groups of the input, each its people's lines. The proofs
--| don't use this: they show the parser's groups from how it reads the
--| input; the tests check this reading of the input against the answers.
def blank (line: List Char): Bool := line.all (char => char == ' ' ∨ char == '\t')

def groupsOf (input: Text): List (List (List Char)) := (input.lines.map Text.toList).splitBy blank

--| "For each group, count the number of questions to which anyone answered
--| 'yes'. What is the sum of those counts?"
def part1Answer (groups: List (List (List Char))): Nat := groups.sumBy (count anyone)

--| "For each group, count the number of questions to which everyone
--| answered 'yes'. What is the sum of those counts?"
def part2Answer (groups: List (List (List Char))): Nat := groups.sumBy (count everyone)
