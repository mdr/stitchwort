--| Advent of Code 2021, day 14: a polymer template (a line of capital
--| letters, each an element), a blank line, then pair insertion rules, one
--| per line, `CH -> B`. A step looks at every pair of neighbouring elements
--| at once and puts the element of that pair's rule (if it has one) between
--| them. Part 1 takes the polymer after 10 steps and subtracts the count of
--| its least common element from the count of its most common one; part 2
--| does the same after 40 steps.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day14.main < inputs/2021/day14.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| Each step nearly doubles the polymer, so after 40 steps it has about 20
--| trillion elements, too many to build. A step only depends on the pairs,
--| though: a pair with a rule becomes two pairs, and pairs that are alike
--| behave alike, so the program keeps how many times each pair occurs.
--| Every element but the first is the second of a pair, and the first never
--| changes, which gives the elements' counts back. Both parts use the pair
--| counts. The parser checks that no two rules are for the same pair. The
--| proofs that the answers are the puzzle's, for every input and any number
--| of steps, are in `Aoc.Year2021.Day14.Proofs` (Proofs/), the tests in
--| `Aoc.Year2021.Day14.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day14
import Std (Bool, Char, Fail, IO, List, Map, Nat, Option, Parse, Text)
import Std.Parse (blankLine, lines, satisfy, takeWhile1, text)

def main(): {IO, Fail} () :=
  let manual := parseManual IO.readAll()
  IO.print "Part 1: ${solvePart1 manual}"
  IO.print "Part 2: ${solvePart2 manual}"

--| Two elements next to each other in a polymer.
type ElementPair = { first: Char, second: Char }

--| A rule `AB -> C`: between the elements of the pair `AB`, insert `C`.
type Rule = { pair: ElementPair, insert: Char }

--| Each pair of neighbouring elements of a polymer, in order.
def pairsOf: List Char → List ElementPair
  | [a, b, ..rest] => [{ first = a, second = b }, ..pairsOf [b, ..rest]]
  | _ => []

--| The puzzle's input: the template, then the rules.
type Manual = { template: List Char, rules: List Rule }

--| The template, a blank line, then one rule per line. Fails if two rules
--| are for the same pair.
def parseManual (input: Text): {Fail} Manual := checkManual (Parse.all input readManual)

def readManual(): {Parse} Manual :=
  let template := takeWhile1 "a capital letter" Char.isAsciiUppercase
  blankLine()
  let rules := lines readRule |> .toList
  { template = template.toList, rules }

def readRule(): {Parse} Rule :=
  let first := element()
  let second := element()
  text " -> "
  let insert := element()
  { pair = { first, second }, insert }

def element(): {Parse} Char := satisfy "a capital letter" Char.isAsciiUppercase

--| The manual, if no two rules are for the same pair; otherwise fail,
--| naming the first pair with two.
def checkManual (manual: Manual): {Fail} Manual := match firstRepeated (manual.rules.map .pair) with
  | Some pair => Fail.fail "two rules for the pair ${pair.first}${pair.second}"
  | None => manual

--| The first pair that is listed again further on.
def firstRepeated: List ElementPair → Option ElementPair
  | [] => None
  | [pair, ..rest] => if rest.contains pair then Some pair else firstRepeated rest

--| What each pair's rule inserts.
def ruleTable (rules: List Rule): Map ElementPair Char := rules.map (rule => (rule.pair, rule.insert)) |> .toMap

--| What a pair becomes in a step: with a rule inserting `c`, the pairs `a c`
--| and `c b`; without one, itself.
def ElementPair.becomes (pair: ElementPair) (table: Map ElementPair Char): List ElementPair := match table.get pair with
  | Some c => [{ first = pair.first, second = c }, { first = c, second = pair.second }]
  | None => [pair]

--| How many times each pair of neighbours occurs.
type PairCounts = Map ElementPair Nat

--| `counts` with each entry's count added at its pair.
def addAll (counts: PairCounts) (entries: List (ElementPair, Nat)): PairCounts :=
  entries.foldLeft counts (sums entry => sums.insertWith entry.fst entry.snd Nat.add)

def countPairs (polymer: List Char): PairCounts := addAll Map.empty (pairsOf polymer |> .map (pair => (pair, 1)))

--| A step on the counts: each pair's count goes to each pair it becomes.
def stepCounts (table: Map ElementPair Char) (counts: PairCounts): PairCounts :=
  addAll Map.empty (counts.toList.flatMap (entry => entry.fst.becomes table |> .map (next => (next, entry.snd))))

--| How many times `element` occurs in a polymer that starts with `first` and
--| has the pair counts `counts`: once for the first element, if it is that,
--| and once for each pair that ends with it.
def elementCount (first: Char) (counts: PairCounts) (element: Char): Nat :=
  Bool.toNat (first == element) + counts.toList.sumBy (entry => if entry.fst.second == element then entry.snd else 0)

--| The count of the most common element less that of the least common, in
--| the polymer `template` has become, whose pair counts are `counts`. The
--| elements looked at are the first and the second of every pair counted,
--| and one counted 0 times is left out. (None is: every count added is at
--| least 1. The filter saves the proofs from showing that.)
def spread (template: List Char) (counts: PairCounts): Nat := match template with
  | [] => 0
  | [first, .._] =>
    let quantities :=
      [first, ..counts.keys.map .second]
        |> .unique
        |> .map (elementCount first counts)
        |> .filter (quantity => 0 < quantity)
    quantities.maximum.getOrElse 0 - quantities.minimum.getOrElse 0

--| The answer after `steps` steps.
def spreadAfter (steps: Nat) (manual: Manual): Nat :=
  spread manual.template (Nat.iterate steps (stepCounts (ruleTable manual.rules)) (countPairs manual.template))

def solvePart1 (manual: Manual): Nat := spreadAfter 10 manual

def solvePart2 (manual: Manual): Nat := spreadAfter 40 manual
