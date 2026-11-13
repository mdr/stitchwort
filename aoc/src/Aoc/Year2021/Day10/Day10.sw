--| Advent of Code 2021, day 10: lines of brackets from four pairs, (), [],
--| {} and <>. A line is corrupted when a closing bracket doesn't match the
--| innermost bracket still open; it is incomplete when it isn't corrupted
--| but leaves brackets open. Part 1 scores each corrupted line by its first
--| wrong closer and adds the scores up. Part 2 completes each incomplete
--| line with the closers it lacks, scores each completion, and takes the
--| middle score.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day10.main < inputs/2021/day10.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| One scan with a stack of the brackets still open settles both parts: it
--| stops at a closer that doesn't match the top of the stack, or ends with
--| the stack, which read top first is the completion. The spec
--| (Spec/Spec.sw) says it with a grammar of balanced lines instead, and the
--| proofs that both answers are the spec's, for every list of lines, are in
--| `Aoc.Year2021.Day10.Proofs` (Proofs/); the tests in
--| `Aoc.Year2021.Day10.Tests` (Tests/). `run` checks neither.

namespace Aoc.Year2021.Day10
import Std (Fail, IO, List, Nat, Parse, Text)

def main(): {IO, Fail} () :=
  let lines := parseLines IO.readAll()
  IO.print "Part 1: ${solvePart1 lines}"
  IO.print "Part 2: ${solvePart2 lines}"

type Bracket = | Round | Square | Curly | Angle

type Token = | Opener (bracket: Bracket) | Closer (bracket: Bracket)

--| Each token's character.
def Token.char: Token → Char
  | Opener Round => '('
  | Opener Square => '['
  | Opener Curly => '{'
  | Opener Angle => '<'
  | Closer Round => ')'
  | Closer Square => ']'
  | Closer Curly => '}'
  | Closer Angle => '>'

--| Every token.
def allTokens: List Token :=
  [Opener Round, Opener Square, Opener Curly, Opener Angle, Closer Round, Closer Square, Closer Curly, Closer Angle]

--| One token per character, one line per line; any other character fails.
--| Each token is read as its own character, so the parser reads exactly
--| the input (`parseReadsLines` in Proofs/Parse.sw).
def parseLines (input: Text): {Fail} List (List Token) := Parse.eachLine input (() => Parse.many token)

def token(): {Parse} Token := Parse.label "a bracket" bracket

--| A token, read as its own character.
def bracket(): {Parse} Token := Parse.pick (allTokens.map (token => (Text.fromList [token.char], token)))

--| Where a scan ends: at the first closer that doesn't match the bracket
--| open innermost (or that nothing is open for), or at the end of the line
--| with the brackets still open, innermost first.
type Scan = | Corrupted (illegal: Bracket) | Unclosed (open: List Bracket)

--| Scans `tokens` with the brackets in `stack` open, innermost first.
def scan (stack: List Bracket): List Token → Scan
  | [] => Unclosed stack
  | [Opener bracket, ..rest] => scan [bracket, ..stack] rest
  | [Closer bracket, ..rest] =>
    match stack with
      | [top, ..below] => if top == bracket then scan below rest else Corrupted bracket
      | [] => Corrupted bracket

def syntaxPoints: Bracket → Nat
  | Round => 3
  | Square => 57
  | Curly => 1197
  | Angle => 25137

--| A corrupted line's score, 0 for any other.
def corruptionScore (line: List Token): Nat := match scan [] line with
  | Corrupted illegal => syntaxPoints illegal
  | Unclosed _ => 0

def solvePart1 (lines: List (List Token)): Nat := lines.sumBy corruptionScore

def completionPoints: Bracket → Nat
  | Round => 1
  | Square => 2
  | Curly => 3
  | Angle => 4

--| Closer by closer: times 5, plus the closer's points.
def completionScore (closers: List Bracket): Nat := closers.foldLeft 0 (score bracket => score * 5 + completionPoints bracket)

--| An incomplete line's completion score; `None` for a corrupted line, or
--| a complete one.
def autocompleteScore (line: List Token): Option Nat := match scan [] line with
  | Corrupted _ => None
  | Unclosed [] => None
  | Unclosed open => Some (completionScore open)

--| The middle of the sorted scores (with an even number of them, the
--| upper of the two middle ones; 0 for none).
def middle (scores: List Nat): Nat := scores.sort.getOr (scores.length / 2) 0

def solvePart2 (lines: List (List Token)): Nat := middle (lines.filterMap autocompleteScore)
