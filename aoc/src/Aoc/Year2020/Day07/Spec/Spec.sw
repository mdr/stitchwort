--| Day 7 as the puzzle states it: the rules as the input writes them, which
--| bags can eventually contain which, and how many bags one holds. The
--| proofs (Proofs/) show the program's answers are these.

namespace Aoc.Year2020.Day07.Spec
import Aoc.Year2020.Day07 (Colour, Content, Rule)
import Std (Char, List, NonEmptyList, Option, Parse, Text)

def shinyGold: Colour := { shade = "shiny", hue = "gold" }

-- The format

--| A word of a colour: one or more letters `a` to `z`.
def Word (word: Text): Prop := word.toList ≠ [] ∧ word.toList.all Char.isAsciiLowercase = True

--| "light red": two words, a space between.
def ColourWritten (read: List Char) (colour: Colour): Prop :=
  read = colour.shade.toList ++ [' ', ..colour.hue.toList] ∧ Word colour.shade ∧ Word colour.hue

--| "1 bright white bag", "2 muted yellow bags": the count in decimal, the
--| colour, and "bag" for one, "bags" otherwise.
def ContentWritten (read: List Char) (content: Content): Prop :=
  ∃ (digits: List Char) => ∃ (colour: List Char) => read
    = digits ++ [' ', ..colour] ++ (if content.count == 1 then " bag" else " bags").toList
    ∧ digits ≠ []
    ∧ digits.all Parse.isDigit = True
    ∧ content.count = Parse.digitsValue digits
    ∧ ColourWritten colour content.colour

--| "no other bags", or the contents with ", " between.
def ContentsWritten (read: List Char) (contents: List Content): Prop :=
  (read = "no other bags".toList ∧ contents = [])
    ∨ (∃ (listed: NonEmptyList Content) => Parse.SepBy ContentWritten (read u => read = ", ".toList) read listed
      ∧ contents = listed.toList)

--| "light red bags contain 1 bright white bag, 2 muted yellow bags."
def RuleWritten (read: List Char) (rule: Rule): Prop :=
  ∃ (colour: List Char) => ∃ (contents: List Char) => read = colour ++ " bags contain ".toList ++ contents ++ ['.']
    ∧ ColourWritten colour rule.colour
    ∧ ContentsWritten contents rule.contents

-- Part 1

--| What the rules say a bag of `colour` must directly contain: the contents
--| of each rule for it. (The puzzle has one rule for each colour.)
def contentsOf (rules: List Rule) (colour: Colour): List Content :=
  rules.filter (rule => rule.colour == colour) |> .flatMap .contents

--| A rule says `outer` bags must directly contain `inner` bags.
def Directly (rules: List Rule) (outer inner: Colour): Prop :=
  ∃ (content: Content) => content ∈ contentsOf rules outer ∧ content.colour = inner

--| Bags going outward from `inner`, each directly inside the next, ending
--| at `outer`.
def Outward (rules: List Rule) (inner: Colour): (bags: List Colour) → (outer: Colour) → Prop
  | [], outer => inner = outer
  | [next, ..rest], outer => Directly rules next inner ∧ Outward rules next rest outer

--| `outer` bags "can eventually contain" `inner` bags: `inner` goes
--| directly inside some bag, which is `outer` or goes outward to it.
def CanContain (rules: List Rule) (outer inner: Colour): Prop :=
  ∃ (holder: Colour) => ∃ (bags: List Colour) => Directly rules holder inner ∧ Outward rules holder bags outer

--| "How many bag colors can eventually contain at least one shiny gold
--| bag?" There are `answer` of them, none counted twice.
def Part1 (rules: List Rule) (answer: Nat): Prop :=
  ∃ (colours: List Colour) => List.Distinct colours
    ∧ (∀ (colour: Colour) => colour ∈ colours ↔ CanContain rules colour shinyGold)
    ∧ answer = colours.length

-- Part 2

--| The bags inside a bag of `colour`: for each of its contents, `count`
--| bags, and the bags inside each of them. Followed at most `depth` bags
--| deep, and `None` if the rules go deeper.
def bagsWithin (rules: List Rule): (depth: Nat) → (colour: Colour) → Option Nat
  | 0, colour => None
  | Succ depth, colour =>
    contentsOf rules colour
      |> .map (content => bagsWithin rules depth content.colour |> .map (inside => content.count * (1 + inside)))
      |> List.allSome
      |> .map List.sum

--| "How many individual bags are required inside your single shiny gold
--| bag?" Rules that settle it at some depth say `total`. Where they go
--| round in a cycle below shiny gold, no depth settles it, and the puzzle
--| has no answer.
def Part2 (rules: List Rule) (total: Nat): Prop := ∃ (depth: Nat) => bagsWithin rules depth shinyGold = Some total
