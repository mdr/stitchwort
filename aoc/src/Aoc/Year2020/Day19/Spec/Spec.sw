--| Day 19 as the puzzle states it, about the received data (`Rule`,
--| `Rules`, `Message`, `Received`): how it is written, what it is for a
--| message to match a rule, and how many messages match rule 0, with the
--| rules as given (part 1) and with rules 8 and 11 replaced (part 2).
--| Nothing else is shared with the program. The proofs (Proofs/) show the
--| program computes these.

namespace Aoc.Year2020.Day19.Spec
import Aoc.Year2020.Day19 (Message, Received, Rule, Rules)
import Std (Char, List, NonEmptyList, Parse, Text)

-- The format

def NumberWritten (read: List Char) (number: Nat): Prop :=
  read ≠ [] ∧ read.all Parse.isDigit = True ∧ number = Parse.digitsValue read

def LetterWritten (read: List Char) (letter: Char): Prop := read = [letter] ∧ letter.isAsciiLowercase = True

--| `4 1 5`: rule numbers with a space between each two.
def SequenceWritten (read: List Char) (sequence: List Nat): Prop :=
  ∃ (numbers: NonEmptyList Nat) => Parse.SepBy NumberWritten (read u => read = [' ']) read numbers
    ∧ sequence = numbers.toList

--| `"a"`, a letter in quotes; or `2 3 | 3 2`, sequences with ` | `
--| between each two.
def RuleWritten: (read: List Char) → (rule: Rule) → Prop
  | read, Letter letter => read = ['"', letter, '"'] ∧ letter.isAsciiLowercase = True
  | read, Alternatives sequences =>
    ∃ (written: NonEmptyList (List Nat)) => Parse.SepBy SequenceWritten (read u => read = " | ".toList) read written
      ∧ sequences = written.toList

--| `1: 2 3 | 3 2`, the rule's number, a colon and a space, the rule.
def NumberedWritten (read: List Char) (numbered: (Nat, Rule)): Prop :=
  ∃ (numberRead: List Char) => ∃ (ruleRead: List Char) => read = numberRead ++ ": ".toList ++ ruleRead
    ∧ NumberWritten numberRead numbered.fst
    ∧ RuleWritten ruleRead numbered.snd

def MessageWritten (read: List Char) (message: Message): Prop :=
  ∃ (letters: NonEmptyList Char) => Parse.Each LetterWritten read letters.toList ∧ message.letters = letters.toList

def LineBreakWritten (read: List Char) (u: ()): Prop := Parse.LineBreak read

--| "The rules for valid messages ... are numbered and build upon each
--| other", one a line; a blank line; the messages, one a line.
def ReceivedWritten (read: List Char) (received: Received): Prop :=
  ∃ (rulesRead: List Char) => ∃ (blank: List Char) => ∃ (messagesRead: List Char) => read
    = rulesRead ++ blank ++ messagesRead
    ∧ (∃ (rules: NonEmptyList (Nat, Rule)) => Parse.SepBy NumberedWritten LineBreakWritten rulesRead rules
      ∧ received.rules.numbered = rules.toList)
    ∧ Parse.BlankLine blank
    ∧ (∃ (messages: NonEmptyList Message) => Parse.SepBy MessageWritten LineBreakWritten messagesRead messages
      ∧ received.messages = messages.toList)

-- Matching

--| The rule numbered `number`. The puzzle numbers each rule once; were a
--| number listed twice, this is the first.
def ruleNumbered (rules: Rules) (number: Nat): Option Rule := rules.numbered.lookup number

--| `Matches rules sequence read`: `read` is matched by the rules of
--| `sequence`, one after another. A rule that is a letter "matches a
--| single character"; one with sequences "means that at least one of the
--| sub-rules must match", each of which is the rules of the sequence "in
--| order".
type Matches (rules: Rules): List Nat → List Char → Prop =
  | MatchesNothing: Matches rules [] []
  | MatchesLetter
      [number: Nat]
      [later: List Nat]
      [letter: Char]
      [rest: List Char]
      (rule: ruleNumbered rules number = Some (Letter letter))
      (laterMatch: Matches rules later rest): Matches rules [number, ..later] [letter, ..rest]
  | MatchesAlternative
      [number: Nat]
      [later: List Nat]
      [read: List Char]
      [rest: List Char]
      (sequences: List (List Nat))
      (rule: ruleNumbered rules number = Some (Alternatives sequences))
      (sequence: List Nat)
      (chosen: sequence ∈ sequences)
      (sequenceMatch: Matches rules sequence read)
      (laterMatch: Matches rules later rest): Matches rules [number, ..later] (read ++ rest)

--| "messages completely match rule 0": all of the message, nothing left.
def MatchesCompletely (rules: Rules) (message: Message): Prop := Matches rules [0] message.letters

--| Part 1: "How many messages completely match rule 0?"
def Part1 (received: Received) (answer: Nat): Prop :=
  List.CountWith (MatchesCompletely received.rules) received.messages answer

--| "replace rules 8: 42 and 11: 42 31 with the following: 8: 42 | 42 8,
--| 11: 42 31 | 42 11 31". Listed first, they are the rules with those
--| numbers.
def loopingRules (rules: Rules): Rules :=
  { numbered = [(8, Alternatives [[42], [42, 8]]), (11, Alternatives [[42, 31], [42, 11, 31]]), ..rules.numbered] }

--| Part 2: "After updating rules 8 and 11, how many messages completely
--| match rule 0?"
def Part2 (received: Received) (answer: Nat): Prop :=
  List.CountWith (MatchesCompletely (loopingRules received.rules)) received.messages answer
