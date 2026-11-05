--| Day 2 as the puzzle states it. The proofs (Proofs/) show the program's
--| checks and counts are these.

namespace Aoc.Year2020.Day02.Spec
import Aoc.Year2020.Day02 (Entry)
import Std (List, Text)

--| "The password policy indicates the lowest and highest number of times a
--| given letter must appear for the password to be valid."
def validPart1 (entry: Entry): Bool :=
  let appearances := (entry.password.toList.filter (== entry.letter)).length
  entry.low <= appearances <= entry.high

--| "Each policy actually describes two positions in the password, where 1
--| means the first character, 2 means the second character, and so on":
--| whether `position` holds the letter.
def holdsLetter (entry: Entry) (position: Nat): Bool :=
  List.withIndexFrom 1 entry.password.toList |> .any (((at, char)) => at == position ∧ char == entry.letter)

--| "Exactly one of these positions must contain the given letter."
def validPart2 (entry: Entry): Bool :=
  ([entry.low, entry.high].filter (position => holdsLetter entry position)).length == 1

--| "How many passwords are valid according to their policies?"
def part1Answer (entries: List Entry): Nat := (entries.filter validPart1).length

def part2Answer (entries: List Entry): Nat := (entries.filter validPart2).length
