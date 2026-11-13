--| Part 1: where the scan stops is the line's first illegal character, and
--| only there; the program's total is the spec's.

namespace Aoc.Year2021.Day10.Proofs
import Aoc.Year2021.Day10 (..)
import Aoc.Year2021.Day10.Spec (..)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Void)

--| The scan of the start ending with `stack` open, and the scan of the rest
--| from there stopping at `illegal`: that closer is the first illegal
--| character of the whole line.
theorem firstIllegalFrom (before: List Token) (illegal: Bracket): ∀ (stack: List Bracket) => scan [] before = Unclosed stack → ∀ (rest: List Token) =>
    scan stack rest = Corrupted illegal → FirstIllegal (before ++ rest) (Closer illegal)
  | stack, open, [], h => cases
  | stack, open, [Opener bracket, ..rest], h =>
    let next := firstIllegalFrom (before ++ [Opener bracket]) illegal [bracket, ..stack] (rewrite scanAppend [] before [Opener bracket], open in rfl) rest h
    rewrite List.appendAssoc before [Opener bracket] rest at next in next
  | [], open, [Closer closer, ..rest], h =>
    rewrite <- corruptedInjective closer illegal h in stopsHere before closer rest [] open (rewrite scanAppend [] before [Closer closer], open in rfl)
  | [top, ..below], open, [Closer closer, ..rest], h =>
    match same: top == closer with
      | True =>
        let opened: scan [] (before ++ [Closer closer]) = Unclosed below := rewrite scanAppend [] before [Closer closer], open, same in rfl
        let next := firstIllegalFrom (before ++ [Closer closer]) illegal below opened rest h
        rewrite List.appendAssoc before [Closer closer] rest at next in next
      | False =>
        rewrite <- corruptedInjective closer illegal h in
          stopsHere before closer rest [top, ..below] open (rewrite scanAppend [] before [Closer closer], open, same in rfl)

--| The scan stops at the closer right after a start it reads to the end.
theorem stopsHere (before: List Token) (closer: Bracket) (rest: List Token) (stack: List Bracket) (open: scan [] before = Unclosed stack)
    (stops: scan [] (before ++ [Closer closer]) = Corrupted closer): FirstIllegal (before ++ [Closer closer, ..rest]) (Closer closer) :=
  At before (Closer closer) rest (legalOfUnclosed before stack open) (legal => notCorruptedOfLegal (before ++ [Closer closer]) closer legal stops)

--| Where the scan stops is the first illegal character.
theorem firstIllegalOfScan (line: List Token) (illegal: Bracket) (h: scan [] line = Corrupted illegal): FirstIllegal line (Closer illegal) :=
  firstIllegalFrom [] illegal [] rfl line h

--| And the first illegal character is always a closer, where the scan
--| stops.
theorem scanOfFirstIllegal (line: List Token) (token: Token): FirstIllegal line token → exists (illegal: Bracket) => token = Closer illegal ∧ scan [] line = Corrupted illegal
  | At before _ after legal illegal =>
    match e: scan [] before with
      | Corrupted stop => Void.exfalso (notCorruptedOfLegal before stop legal e)
      | Unclosed stack =>
        match token with
          | Opener bracket => Void.exfalso (illegal (legalOpener before bracket legal))
          | Closer closer =>
            match stack with
              | [] => Witness closer (Both rfl (rewrite scanAppend [] before [Closer closer, ..after], e in rfl))
              | [top, ..below] =>
                match same: top == closer with
                  | True => Void.exfalso (illegal (legalOfUnclosed (before ++ [Closer closer]) below (rewrite scanAppend [] before [Closer closer], e, same in rfl)))
                  | False => Witness closer (Both rfl (rewrite scanAppend [] before [Closer closer, ..after], e, same in rfl))

--| A line has at most one first illegal character.
theorem firstIllegalUnique (line: List Token) (a: Token) (b: Token) (first: FirstIllegal line a) (second: FirstIllegal line b): a = b :=
  match scanOfFirstIllegal line a first with
    | Witness x (Both isX stopsX) =>
      match scanOfFirstIllegal line b second with
        | Witness y (Both isY stopsY) => rewrite isX, isY, corruptedInjective x y (Eq.trans (Eq.sym stopsX) stopsY) in rfl

theorem pointsAgree (bracket: Bracket): syntaxPoints bracket = errorPoints bracket := cases

--| Each line's score is the spec's.
theorem lineErrorScore (line: List Token): ErrorScore line (corruptionScore line) := match e: scan [] line with
  | Corrupted illegal => rewrite pointsAgree illegal in Illegal (firstIllegalOfScan line illegal e)
  | Unclosed stack => NotCorrupted (legalOfUnclosed line stack e)

--| Part 1 is the total syntax error score, for every list of lines.
theorem part1Correct (lines: List (List Token)): Part1Answer lines (solvePart1 lines) := match lines with
  | [] => NoLines
  | [line, ..rest] => rewrite List.sumByCons rest line corruptionScore in NextLine (lineErrorScore line) (part1Correct rest)

def bracketOf: Token → Bracket
  | Opener bracket => bracket
  | Closer bracket => bracket

--| A line has one syntax error score.
theorem errorScoreUnique (line: List Token) (a: Nat) (b: Nat): ErrorScore line a → ErrorScore line b → a = b
  | Illegal [bracket := x] first, Illegal [bracket := y] second => rewrite Eq.cong bracketOf (firstIllegalUnique line (Closer x) (Closer y) first second) in rfl
  | Illegal [bracket := x] first, NotCorrupted legal => Void.exfalso (illegalNotLegal line x first legal)
  | NotCorrupted legal, Illegal [bracket := y] second => Void.exfalso (illegalNotLegal line y second legal)
  | NotCorrupted _, NotCorrupted _ => rfl

--| A line with an illegal character isn't legal.
theorem illegalNotLegal (line: List Token) (illegal: Bracket) (first: FirstIllegal line (Closer illegal)) (legal: Legal line): Void :=
  match scanOfFirstIllegal line (Closer illegal) first with
    | Witness x (Both _ stops) => notCorruptedOfLegal line x legal stops

--| So the spec's part 1 answer is unique: the program's is the only one.
theorem part1Unique (lines: List (List Token)) (a: Nat) (b: Nat): Part1Answer lines a → Part1Answer lines b → a = b
  | NoLines, NoLines => rfl
  | NextLine [score := s] [total := t] first rest, NextLine [score := s2] [total := t2] second rest2 =>
    rewrite errorScoreUnique _ s s2 first second, part1Unique _ t t2 rest rest2 in rfl
