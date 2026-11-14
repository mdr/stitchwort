--| Day 10 as the puzzle states it, with no stack: which lines are balanced
--| is a grammar, a character is illegal when the line up to it can't be
--| finished as a balanced line, and a completion is closers that finish
--| it. The program's tokens are the only thing shared with it. The proofs
--| (Proofs/) show the program computes these answers, for every list of
--| lines.

namespace Aoc.Year2021.Day10.Spec
import Aoc.Year2021.Day10 (Bracket, Token)
import Std (Exists, List, Nat)

--| Balanced lines (the puzzle's chunks): the empty line, two balanced lines
--| one after the other, or a balanced line between an opener and the closer
--| of the same pair.
type Balanced: List Token → Prop =
  | Empty: Balanced []
  | Concat (first: Balanced xs) (second: Balanced ys): Balanced (xs ++ ys)
  | Wrap (bracket: Bracket) (inner: Balanced xs): Balanced [Opener bracket, ..xs ++ [Closer bracket]]

--| A start of a line that some ending finishes as a balanced line.
def Legal (start: List Token): Prop := exists (ending: List Token) => Balanced (start ++ ending)

--| The first illegal character of a line: the tokens before it can be
--| finished, and those up to and including it can't. (Every start of a
--| legal start is legal, so no earlier character is illegal:
--| `legalOfLonger` in the proofs.)
type FirstIllegal: List Token → Token → Prop =
  | At
      (before: List Token)
      (token: Token)
      (after: List Token)
      (legal: Legal before)
      (illegal: ¬(Legal (before ++ [token]))): FirstIllegal (before ++ [token, ..after]) token

--| The syntax error score of each illegal closer.
def errorPoints: Bracket → Nat
  | Round => 3
  | Square => 57
  | Curly => 1197
  | Angle => 25137

--| A line's syntax error score: its first illegal character's points if it
--| is corrupted, otherwise 0.
type ErrorScore: List Token → Nat → Prop =
  | Illegal (first: FirstIllegal line (Closer bracket)): ErrorScore line (errorPoints bracket)
  | NotCorrupted (legal: Legal line): ErrorScore line 0

--| Part 1: the total syntax error score of the lines.
type Part1Answer: List (List Token) → Nat → Prop =
  | NoLines: Part1Answer [] 0
  | NextLine
      (line: ErrorScore first score)
      (rest: Part1Answer lines total): Part1Answer [first, ..lines] (score + total)

--| An incomplete line: not corrupted, but not balanced either.
def Incomplete (line: List Token): Prop := Legal line ∧ ¬(Balanced line)

--| A completion of a line: closers, in order, that make it balanced. A
--| line has at most one (`completionUnique` in the proofs).
def Completes (line: List Token) (closers: List Bracket): Prop := Balanced (line ++ closers.map Closer)

def autocompletePoints: Bracket → Nat
  | Round => 1
  | Square => 2
  | Curly => 3
  | Angle => 4

--| A completion's score: start at 0, and for each closer multiply by 5 and
--| add its points.
def completionTotal (score: Nat): List Bracket → Nat
  | [] => score
  | [closer, ..rest] => completionTotal (score * 5 + autocompletePoints closer) rest

--| The completion scores of the incomplete lines, in order.
type CompletionScores: List (List Token) → List Nat → Prop =
  | NoneLeft: CompletionScores [] []
  | Scored
      (incomplete: Incomplete first)
      (completes: Completes first closers)
      (rest: CompletionScores lines scores): CompletionScores [first, ..lines] [completionTotal 0 closers, ..scores]
  | Skipped
      (complete: ¬(Incomplete first))
      (rest: CompletionScores lines scores): CompletionScores [first, ..lines] scores

--| The middle score: one of the scores, with at most half of them smaller
--| and at most half larger. With an odd number of scores, as the puzzle
--| promises, there is exactly one (`middleUnique` in the proofs); with an
--| even number, either of the two middle ones is.
def Middle (scores: List Nat) (middle: Nat): Prop :=
  middle ∈ scores
    ∧ 2 * scores.count (score => score < middle) ≤ scores.length
    ∧ 2 * scores.count (score => middle < score) ≤ scores.length

--| Part 2: the middle completion score.
def Part2Answer (lines: List (List Token)) (answer: Nat): Prop :=
  exists (scores: List Nat) => CompletionScores lines scores ∧ Middle scores answer
