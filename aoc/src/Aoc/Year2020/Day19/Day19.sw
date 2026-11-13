--| Advent of Code 2020, day 19: Monster Messages. The input is a list of
--| numbered rules, then a list of messages of `a`s and `b`s. A rule is a
--| letter (`4: "a"`), or alternatives separated by `|`, each a sequence of
--| rule numbers to match one after another (`1: 2 3 | 3 2`). Each part is
--| how many messages match rule 0 completely; in part 2, rules 8 and 11 are
--| replaced by ones that refer to themselves, so they can repeat.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day19.main < inputs/2020/day19.txt
--|
--| One matcher serves both parts: given a start of the message, it gives
--| every way a rule can match a start of it, as what is left after each,
--| so a rule that can repeat is no special case. `fuel` bounds the depth of
--| rules within rules; `Rules.enough` is enough for the puzzle's rules
--| (`Rules.productive` says when). The proofs, that the parser reads the
--| puzzle's format and that a message matches exactly when the puzzle says
--| it does, are in `Aoc.Year2020.Day19.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2020.Day19.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2020.Day19
import Std (Char, Fail, IO, List, Map, Nat, Option, Parse, Text)

def main(): {IO, Fail} () :=
  let received := parseReceived IO.readAll()
  IO.print "Part 1: ${received.matchingCount}"
  IO.print "Part 2: ${received.withLoops.matchingCount}"

type Rule =
  | Letter (letter: Char)
  | Alternatives (sequences: List (List Nat))

--| The rules with their numbers, as the input lists them.
type Rules = { numbered: List (Nat, Rule) }

--| The rule with this number, the first if two have it.
def Rules.rule (rules: Rules) (number: Nat): Option Rule := rules.numbered.lookup number

--| The rules by number, for looking one up without going down the list.
--| Entries earlier in the list win, so it agrees with [`Rules.rule`]
--| (`Aoc.Year2020.Day19.Proofs.tableRule`).
def ruleTable: (entries: List (Nat, Rule)) → Map Nat Rule
  | [] => Map.empty
  | [(number, rule), ..later] => ruleTable later |> .insert number rule

type Message = { letters: List Char }

type Received = { rules: Rules, messages: List Message }

-- The format

def letter(): {Parse} Char := Parse.satisfy "a letter" Char.isAsciiLowercase

def sequence(): {Parse} List Nat := Parse.sepBy1 Parse.nat (() => Parse.char ' ') |> .toList

def ruleBody(): {Parse} Rule :=
  Parse.oneOf [
    () =>
      Parse.char '"'
      let found := letter()
      Parse.char '"'
      Letter found,
    () =>
      let sequences := Parse.sepBy1 sequence (() => Parse.text " | ")
      Alternatives sequences.toList
  ]

def numberedRule(): {Parse} (Nat, Rule) :=
  let number := Parse.nat()
  Parse.text ": "
  let rule := ruleBody()
  (number, rule)

def message(): {Parse} Message :=
  let letters := Parse.many1 letter
  { letters = letters.toList }

def received(): {Parse} Received :=
  let rules := Parse.lines numberedRule
  Parse.blankLine()
  let messages := Parse.lines message
  { rules = { numbered = rules.toList }, messages = messages.toList }

def parseReceived (input: Text): {Fail} Received := Parse.all input received

-- Matching

--| What is left of `message` after a letter rule: the rest, if it starts
--| with that letter.
def leftAfterLetter (letter: Char) (message: List Char): List (List Char) := match message with
  | [first, ..rest] => if first == letter then [rest] else []
  | [] => []

--| What can be left of `message` after rule `number` matches a start of
--| it, one entry for each way it can, with `rule` giving the rule for a
--| number. Each rule within a rule takes one `fuel`; with none left,
--| nothing matches.
def leftAfterWith (rule: Nat → Option Rule) (fuel: Nat) (number: Nat) (message: List Char): List (List Char) :=
  match fuel with
    | Zero => []
    | Succ more =>
      match rule number with
        | None => []
        | Some (Letter letter) => leftAfterLetter letter message
        | Some (Alternatives sequences) => sequences.flatMap (sequence => leftAfterAllWith rule more sequence message)

--| What can be left of `message` after the rules of `sequence` match a
--| start of it, one after another.
def leftAfterAllWith (rule: Nat → Option Rule) (fuel: Nat) (sequence: List Nat) (message: List Char): List (List Char) :=
  match sequence with
    | [] => [message]
    | [number, ..later] => leftAfterWith rule fuel number message |> .flatMap (left => leftAfterAllWith rule fuel later left)

--| [`leftAfterWith`] looking rules up in the list, the first with a number.
def Rules.leftAfter (rules: Rules) (fuel: Nat) (number: Nat) (message: List Char): List (List Char) :=
  leftAfterWith rules.rule fuel number message

def Rules.leftAfterAll (rules: Rules) (fuel: Nat) (sequence: List Nat) (message: List Char): List (List Char) :=
  leftAfterAllWith rules.rule fuel sequence message

--| A rule's alternatives are never empty, and a rule's alternative that
--| is one rule leads to a lower `rank`. Then every rule reads a letter, and
--| a rule can't come back to itself without reading one.
def Rules.productiveWith (rules: Rules) (rank: Nat → Nat): Bool :=
  rules.numbered.all (entry =>
    match entry.snd with
      | Letter letter => True
      | Alternatives sequences =>
        sequences.all (sequence =>
          match sequence with
            | [] => False
            | [only] => rank only < rank entry.fst
            | [first, second, ..more] => True))

--| The longest chain of one-rule alternatives from rule `number`, up to
--| `fuel` long.
def Rules.chain (rules: Rules) (fuel: Nat) (number: Nat): Nat := match fuel with
  | Zero => 0
  | Succ more =>
    match rules.rule number with
      | Some (Alternatives sequences) => sequences.map (rules.chainThrough more) |> .maximum |> .getOrElse 0
      | _ => 0

--| The longest chain through an alternative: none unless it is one rule.
def Rules.chainThrough (rules: Rules) (fuel: Nat): (sequence: List Nat) → Nat
  | [] => 0
  | [only] => rules.chain fuel only + 1
  | [first, second, ..more] => 0

--| More than any chain of one-rule alternatives can be long, when no rule
--| can come back to itself through them.
def Rules.rankBound (rules: Rules): Nat := rules.numbered.length + 2

def Rules.rank (rules: Rules) (number: Nat): Nat := rules.chain (rules.numbered.length + 1) number

def Rules.productive (rules: Rules): Bool := rules.productiveWith rules.rank

--| Fuel for a message: each rule within a rule either reads a letter more
--| or follows a chain of one-rule alternatives a step.
def Rules.enough (rules: Rules) (message: Message): Nat := (message.letters.length + 1) * rules.rankBound

--| Whether the rule 0 matches the whole message. The rules are looked up
--| in a table made for the call, so a caller matching many messages
--| should share it with [`Rules.matchesCompletelyIn`].
def Rules.matchesCompletely (rules: Rules) (message: Message): Bool := rules.matchesCompletelyIn (ruleTable rules.numbered) message

def Rules.matchesCompletelyIn (rules: Rules) (table: Map Nat Rule) (message: Message): Bool :=
  leftAfterWith table.get (rules.enough message) 0 message.letters |> .any .isEmpty

def Received.matchingCount (received: Received): Nat :=
  let table := ruleTable received.rules.numbered
  received.messages.count (received.rules.matchesCompletelyIn table)

--| Part 2: "replace rules 8: 42 and 11: 42 31 with 8: 42 | 42 8 and 11:
--| 42 31 | 42 11 31". Put first, they're the rules with those numbers.
def Received.withLoops (received: Received): Received :=
  { received | rules = { numbered = [(8, Alternatives [[42], [42, 8]]), (11, Alternatives [[42, 31], [42, 11, 31]]), ..received.rules.numbered] } }
