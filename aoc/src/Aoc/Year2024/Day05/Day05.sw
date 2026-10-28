-- Advent of Code 2024, day 5: page ordering rules ("47|53": page 47 must be
-- printed before page 53), a blank line, then updates, each a list of pages
-- ("75,47,61,53,29"). Part 1 adds up the middle pages of the updates already
-- in the right order; part 2 puts the others in the right order and adds up
-- their middle pages.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day05.main < inputs/2024/day05.txt
--
-- The proofs are in `Aoc.Year2024.Day05.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day05.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day05
import Std (Fail, IO, List, Nat, Parse, Set, Text)
import Std.Parse (blankLine, char, lines, nat, sepBy1)

def main(): {IO, Fail} () :=
  let queue := parsePrintQueue IO.readAll()
  IO.print "Part 1: ${solvePart1 queue}"
  IO.print "Part 2: ${solvePart2 queue}"

-- "X|Y": page X must be printed before page Y.
type Rule = { before: Nat, after: Nat }

-- The pages of one update, in the order they are printed.
type Update = { pages: List Nat }

type PrintQueue = { rules: List Rule, updates: List Update }

-- "47|53".
def rule(): {Parse} Rule :=
  let before := nat()
  char '|'
  let after := nat()
  { before, after }

-- "75,47,61,53,29".
def update(): {Parse} Update := { pages = sepBy1 nat (() => char ',') }

-- The rules, one per line, a blank line, then the updates, one per line.
def printQueue(): {Parse} PrintQueue :=
  let rules := lines rule
  blankLine()
  let updates := lines update
  { rules, updates }

def parsePrintQueue (input: Text): {Fail} PrintQueue := Parse.all input printQueue

-- The rules as a set of (before, after) pairs, for quick lookup.
def ruleSet (rules: List Rule): Set (Nat, Nat) := rules.map (rule => (rule.before, rule.after)) |> Set.fromList

-- Whether a rule says `earlier` must be printed before `later`.
def mustPrecede (rules: Set (Nat, Nat)) (earlier: Nat) (later: Nat): Bool := rules.contains (earlier, later)

-- No page is followed by one that must be printed before it.
def inOrder (precedes: Nat → Nat → Bool): List Nat → Bool
  | Nil => True
  | Cons page later => later.all (laterPage => !(precedes laterPage page)) && inOrder precedes later

-- The pages sorted so that each comes before the next unless a rule says
-- otherwise.
def reorder (precedes: Nat → Nat → Bool) (update: Update): Update :=
  { pages = update.pages.sortWith (page next => !(precedes next page)) }

-- The page in the middle of an update (updates have an odd number of pages).
def middlePage (update: Update): Nat := update.pages.getOr (update.pages.length / 2) 0

def solvePart1 (queue: PrintQueue): Nat :=
  let precedes := mustPrecede (ruleSet queue.rules)
  queue.updates.filter (update => inOrder precedes update.pages) |> .sumBy middlePage

def solvePart2 (queue: PrintQueue): Nat :=
  let precedes := mustPrecede (ruleSet queue.rules)
  queue.updates.filter (update => !(inOrder precedes update.pages))
    |> .map (reorder precedes)
    |> .sumBy middlePage
