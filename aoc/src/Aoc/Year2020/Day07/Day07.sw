--| Advent of Code 2020, day 7: luggage rules. Each line says what a bag of
--| one colour must directly contain: "light red bags contain 1 bright white
--| bag, 2 muted yellow bags." Part 1 counts the colours that can eventually
--| contain a shiny gold bag; part 2 counts the bags a shiny gold bag holds
--| in all.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day07.main < inputs/2020/day07.txt
--|
--| Part 1 walks outward from shiny gold, from each bag to the bags that hold
--| it, with std's `Graph.reachable`; part 2 follows the rules inward.
--| The proofs, that the parser reads the puzzle's format and that both
--| answers are the puzzle's, are in `Aoc.Year2020.Day07.Proofs` (Proofs/),
--| and the tests in `Aoc.Year2020.Day07.Tests` (Tests/); `run` checks
--| neither.

namespace Aoc.Year2020.Day07
import Std (Char, Eq, Exists, Fail, Graph, IO, List, Map, NonEmptyList, Option, Pair, Parse, Set, Text)

def main(): {IO, Fail} () :=
  let rules := parseRules IO.readAll()
  IO.print "Part 1: ${solvePart1 rules}"
  let total := solvePart2 rules
  IO.print "Part 2: ${total}"

--| A bag's colour, two words: "light red", "shiny gold".
type Colour = { shade: Text, hue: Text }

def Colour.name (colour: Colour): Text := "${colour.shade} ${colour.hue}"

def shinyGold: Colour := { shade = "shiny", hue = "gold" }

--| One part of a rule: "2 muted yellow bags".
type Content = { count: Nat, colour: Colour }

--| What a bag of `colour` must directly contain.
type Rule = { colour: Colour, contents: List Content }

type Rules = { all: List Rule }

def word(): {Parse} Text := Parse.takeWhile1 "a colour, 'a' to 'z'" Char.isAsciiLowercase

def colour(): {Parse} Colour :=
  let shade := word()
  Parse.char ' '
  let hue := word()
  { shade, hue }

def content(): {Parse} Content :=
  let count := Parse.nat()
  Parse.char ' '
  let colour := colour()
  Parse.text (if count == 1 then " bag" else " bags")
  { count, colour }

def contentList(): {Parse} List Content := Parse.sepBy1 content (() => Parse.text ", ") |> .toList

def contents(): {Parse} List Content := Parse.oneOf [() => Parse.before ([]: List Content) "no other bags", contentList]

def rule(): {Parse} Rule :=
  let colour := colour()
  Parse.text " bags contain "
  let contents := contents()
  Parse.char '.'
  { colour, contents }

def parseRules (input: Text): {Fail} Rules := { all = Parse.eachLine input rule }

--| A rule lists `inside` among the contents of `holder`.
type Holding = { inside: Colour, holder: Colour }

def Rule.holdings (rule: Rule): List Holding := rule.contents.map (content => { inside = content.colour, holder = rule.colour })

type Holders = { byInside: Map Colour (NonEmptyList Holding) }

def Rules.holders (rules: Rules): Holders := { byInside = rules.all.flatMap .holdings |> .groupBy .inside }

--| The colours whose rules list `colour`.
def Holders.of (holders: Holders) (colour: Colour): List Colour := match holders.byInside.get colour with
  | Some holdings => holdings.toList.map .holder
  | None => []

--| Bags and the bags that hold them, each step out costing 1.
def Rules.graph (rules: Rules): Graph Colour :=
  let holders := rules.holders
  Graph.fromEdges (colour => holders.of colour |> .map (holder => (holder, 1))) (rules.all.map .colour)

--| The colours that can eventually contain a bag of `colour`.
def Rules.outside (rules: Rules) (colour: Colour): Set Colour :=
  let graph := rules.graph
  graph.reachable (graph.edges colour |> .map Pair.fst)

def solvePart1 (rules: Rules): Nat := (rules.outside shinyGold).size

type RuleBook = { byColour: Map Colour (NonEmptyList Rule) }

def Rules.book (rules: Rules): RuleBook := { byColour = rules.all.groupBy .colour }

def RuleBook.contentsOf (book: RuleBook) (colour: Colour): List Content := match book.byColour.get colour with
  | Some found => found.toList.flatMap .contents
  | None => []

--| The bags inside a bag of `colour`, following the rules at most `depth`
--| bags deep: `None` if they go deeper.
def RuleBook.bagsToDepth (book: RuleBook): (depth: Nat) → (colour: Colour) → Option Nat
  | 0, colour => None
  | Succ depth, colour =>
    book.contentsOf colour
      |> .map (content => book.bagsToDepth depth content.colour |> .map (inside => content.count * (1 + inside)))
      |> List.allSome
      |> .map List.sum

--| Without a cycle, a chain of bags inward repeats no colour, so it has at
--| most one bag more than there are rules.
def Rules.bagsInside (rules: Rules) (colour: Colour): {Fail} Nat :=
  match rules.book.bagsToDepth (rules.all.length + 1) colour with
    | Some total => total
    | None => Fail.fail "the rules for ${colour.name} bags go round in a cycle"

def solvePart2 (rules: Rules): {Fail} Nat := rules.bagsInside shinyGold
