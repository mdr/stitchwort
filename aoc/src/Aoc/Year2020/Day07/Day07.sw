--| Advent of Code 2020, day 7: luggage rules. Each line says what a bag of
--| one colour must directly contain: "light red bags contain 1 bright white
--| bag, 2 muted yellow bags." Part 1 counts the colours that can eventually
--| contain a shiny gold bag; part 2 counts the bags a shiny gold bag holds
--| in all.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day07.main < inputs/2020/day07.txt
--|
--| Part 1 walks outward from shiny gold, from each bag to the bags that hold
--| it, with std's breadth-first search; part 2 follows the rules inward.
--| The proofs, that the parser reads the puzzle's format and that both
--| answers are the puzzle's, are in `Aoc.Year2020.Day07.Proofs` (Proofs/),
--| and the tests in `Aoc.Year2020.Day07.Tests` (Tests/); `run` checks
--| neither.

namespace Aoc.Year2020.Day07
import Std (Char, Eq, Exists, Fail, Graph, IO, List, Map, NonEmptyList, Option, Pair, Parse, Text)

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

--| Each colour a rule lists, with the rule's own colour: (inside, holder).
def Rule.insides (rule: Rule): List (Colour, Colour) := rule.contents.map (content => (content.colour, rule.colour))

--| Each colour, with the colours whose rules list it.
def holdersIndex (rules: List Rule): Map Colour (NonEmptyList (Colour, Colour)) := rules.flatMap .insides |> .groupBy Pair.fst

def holdersIn (index: Map Colour (NonEmptyList (Colour, Colour))) (colour: Colour): List Colour :=
  match index.get colour with
    | Some pairs => pairs.toList.map Pair.snd
    | None => []

theorem holdersInIndex (rules: List Rule) (colour: Colour):
    holdersIn (holdersIndex rules) colour = ((rules.flatMap .insides).filter (pair => Map.Spec.sameKey colour pair.fst)).map Pair.snd :=
  rewrite Map.getGroupBy Pair.fst colour (rules.flatMap .insides) in
    match List.filter (rules.flatMap .insides) (pair => Map.Spec.sameKey colour pair.fst) with
      | [] => rfl
      | [first, ..rest] => rfl

--| Every holder is the colour of a rule.
theorem holderListed (rules: List Rule) (colour: Colour) (holder: Colour) (found: holder ∈ holdersIn (holdersIndex rules) colour):
    holder ∈ rules.map .colour :=
  let (Witness pair (Both kept same)) := List.memMapElim Pair.snd holder _ (rewrite holdersInIndex rules colour at found in found)
  let (Both listed matching) := List.memFilter _ _ kept
  List.anyElim (rule => pair ∈ rule.insides) (holder ∈ rules.map .colour) rules (List.memFlatMapElim .insides pair rules listed)
    (rule member inRule =>
      let (Witness content (Both inContents made)) := List.memMapElim (content => (content.colour, rule.colour)) pair rule.contents inRule
      rewrite <- same, <- made in List.memMap rules rule member .colour)

--| Bags and the bags that hold them, each step out costing 1.
def Rules.graph (rules: Rules): Graph Colour :=
  let index := holdersIndex rules.all
  {
    edges = colour => holdersIn index colour |> .map (holder => (holder, 1)),
    states = rules.all.map .colour,
    listed = colour holder weight edge =>
      let (Witness listed (Both found same)) := List.memMapElim (holder => (holder, 1)) (holder, weight) _ edge
      holderListed rules.all colour holder (rewrite <- Eq.cong Pair.fst same in found)
  }

--| The colours that can eventually contain a bag of `colour`, each with the
--| fewest steps out from its first holder.
def Rules.outside (rules: Rules) (colour: Colour): Map Colour Nat :=
  let graph := rules.graph
  graph.breadthFirst (graph.edges colour |> .map Pair.fst)

def solvePart1 (rules: Rules): Nat := (rules.outside shinyGold).size

def Rules.byColour (rules: Rules): Map Colour (NonEmptyList Rule) := rules.all.groupBy .colour

def contentsIn (index: Map Colour (NonEmptyList Rule)) (colour: Colour): List Content :=
  match index.get colour with
    | Some found => found.toList.flatMap .contents
    | None => []

--| The bags inside a bag of `colour`, following the rules at most `depth`
--| bags deep: `None` if they go deeper.
def bagsInside (index: Map Colour (NonEmptyList Rule)): (depth: Nat) → (colour: Colour) → Option Nat
  | 0, colour => None
  | Succ depth, colour =>
    contentsIn index colour
      |> .map (content => bagsInside index depth content.colour |> .map (inside => content.count * (1 + inside)))
      |> List.allSome
      |> .map List.sum

--| Without a cycle, a chain of bags inward repeats no colour, so it has at
--| most one bag more than there are rules.
def Rules.bagsInside (rules: Rules) (colour: Colour): {Fail} Nat :=
  match bagsInside rules.byColour (rules.all.length + 1) colour with
    | Some total => total
    | None => Fail.fail "the rules for ${colour.name} bags go round in a cycle"

def solvePart2 (rules: Rules): {Fail} Nat := rules.bagsInside shinyGold
