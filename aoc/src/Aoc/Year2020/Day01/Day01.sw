--| Advent of Code 2020, day 1: an expense report, one number per line. Part 1
--| finds the two entries that sum to 2020 and multiplies them; part 2 does the
--| same for three entries.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day01.main < inputs/2020/day01.txt
--|
--| The puzzle input is committed in aoc/inputs/2020/.
--|
--| Part 1 doesn't try every pair: it reads the entries once, keeping a set of
--| those seen, and stops at the first entry whose partner (2020 minus it) was
--| seen before it. Part 2 tries each entry as the first of the three and looks
--| for a pair after it summing to the rest, so it takes n searches of part 1's
--| kind instead of n³ triples. The proofs, that what they find are entries
--| summing to 2020 and that they find one whenever there is one, are in
--| `Aoc.Year2020.Day01.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2020.Day01.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2020.Day01
import Std (Fail, IO, List, Option, Parse, Set)
import Std.Parse (nat, token)

def main(): {IO, Fail} () :=
  let entries := parseEntries IO.readAll()
  IO.print "Part 1: ${solvePart1 entries |> .orFail "no two entries sum to 2020"}"
  IO.print "Part 2: ${solvePart2 entries |> .orFail "no three entries sum to 2020"}"

--| One entry per line, spaces around it allowed. Anything else fails, naming
--| the line and column.
def parseEntries (input: Text): {Fail} List Nat := Parse.eachLine input (() => token nat)

def solvePart1 (entries: List Nat): Option Nat := findPair 2020 entries |> .map (((a, b)) => a * b)

def solvePart2 (entries: List Nat): Option Nat := findTriple 2020 entries |> .map (((a, b, c)) => a * b * c)

--| Two entries summing to `target`, the earlier one first.
def findPair (target: Nat) (entries: List Nat): Option (Nat, Nat) := findPairAfter target Set.empty entries

--| The first entry of `entries` whose partner, `target` minus it, is in
--| `seen`, with that partner; each entry is added to `seen` as it is passed.
def findPairAfter (target: Nat) (seen: Set Nat): List Nat → Option (Nat, Nat)
  | [] => None
  | [x, ..rest] =>
    if x <= target ∧ seen.contains (target - x) then Some (target - x, x) else findPairAfter target (seen.insert x) rest

--| Three entries summing to `target`, in the order they come.
def findTriple (target: Nat): List Nat → Option (Nat, Nat, Nat)
  | [] => None
  | [x, ..rest] =>
    match (if x <= target then findPair (target - x) rest else None) with
      | Some (b, c) => Some (x, b, c)
      | None => findTriple target rest
