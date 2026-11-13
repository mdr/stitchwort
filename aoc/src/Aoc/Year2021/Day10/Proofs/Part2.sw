--| Part 2: what the scan leaves open, closed innermost first, is a line's
--| one completion; the program's scores are the spec's, and its middle is
--| the spec's middle (Middle.sw).

namespace Aoc.Year2021.Day10.Proofs
import Aoc.Year2021.Day10 (..)
import Aoc.Year2021.Day10.Spec (..)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Void)

def openOr (fallback: List Bracket): Scan → List Bracket
  | Corrupted _ => fallback
  | Unclosed open => open

theorem unclosedInjective ∀ (a: List Bracket) (b: List Bracket) (h: Unclosed a = Unclosed b): a = b := Eq.cong (openOr a) h

--| A balanced line's scan ends with nothing open.
theorem balancedScanNil ∀ (line: List Token) (balanced: Balanced line): scan [] line = Unclosed [] :=
  let whole := balancedScan [] [] balanced
  rewrite List.appendNil line at whole in whole

--| Closing what the scan leaves open completes the line.
theorem completesOfUnclosed ∀ [line: List Token] [stack: List Bracket] (h: scan [] line = Unclosed stack): Completes line stack :=
  scanBalanced (line ++ stack.map Closer) (rewrite scanAppend [] line (stack.map Closer), h in closeAll stack)

--| Only the open brackets, closed innermost first, close them all.
theorem closersExact ∀ (stack closers: List Bracket) (h: scan stack (closers.map Closer) = Unclosed []): closers = stack :=
  match stack, closers with
    | stack, [] => Eq.sym (unclosedInjective stack [] h)
    | [top, ..below], [closer, ..rest] =>
      match same: top == closer with
        | True => rewrite closersExact below rest h, same.read in rfl

--| Any completion of a line is what its scan leaves open.
theorem completionIsOpen ∀ (line: List Token) (stack: List Bracket) (open: scan [] line = Unclosed stack) (closers: List Bracket) (completes: Completes line closers):
    closers = stack :=
  let whole := balancedScanNil (line ++ closers.map Closer) completes
  closersExact stack closers (rewrite scanAppend [] line (closers.map Closer), open at whole in whole)

--| A line has at most one completion.
theorem completionUnique ∀ (line: List Token) (a: List Bracket) (b: List Bracket) (first: Completes line a) (second: Completes line b): a = b :=
  match e: scan [] line with
    | Corrupted illegal => Void.exfalso (notCorruptedOfLegal line illegal (Witness (a.map Closer) first) e)
    | Unclosed stack => rewrite completionIsOpen line stack e a first, completionIsOpen line stack e b second in rfl

--| A line whose scan leaves something open is incomplete.
theorem incompleteOfUnclosed ∀ (line: List Token) (top: Bracket) (below: List Bracket) (e: scan [] line = Unclosed [top, ..below]): Incomplete line :=
  Both (legalOfUnclosed line [top, ..below] e)
    (balanced =>
      let closed: Unclosed [top, ..below] = Unclosed [] := Eq.trans (Eq.sym e) (balancedScanNil line balanced)
      cases)

theorem completionPointsAgree ∀ (bracket: Bracket): completionPoints bracket = autocompletePoints bracket := cases

theorem completionFold ∀ (closers: List Bracket) (score: Nat):
    closers.foldLeft score (total bracket => total * 5 + completionPoints bracket) = completionTotal score closers :=
  match closers with
    | [] => rfl
    | [bracket, ..rest] => rewrite <- completionPointsAgree bracket in completionFold rest (score * 5 + completionPoints bracket)

--| The program's scores are the incomplete lines' completion scores, in
--| order.
theorem completionScoresCorrect ∀ (lines: List (List Token)): CompletionScores lines (lines.filterMap autocompleteScore) :=
  match lines with
    | [] => NoneLeft
    | [line, ..rest] =>
      match e: scan [] line with
        | Corrupted illegal => Skipped (incomplete => notCorruptedOfLegal line illegal (And.left incomplete) e) (completionScoresCorrect rest)
        | Unclosed [] => Skipped (incomplete => And.right incomplete (scanBalanced line e)) (completionScoresCorrect rest)
        | Unclosed [top, ..below] =>
          rewrite completionFold [top, ..below] 0 in
            Scored [closers := [top, ..below]] (incompleteOfUnclosed line top below e) (completesOfUnclosed e) (completionScoresCorrect rest)

--| The spec's list of completion scores is unique.
theorem completionScoresUnique ∀ (lines: List (List Token)) (a: List Nat) (b: List Nat): CompletionScores lines a → CompletionScores lines b → a = b
  | NoneLeft, NoneLeft => rfl
  | Scored [closers := x] [scores := xs] _ first rest, Scored [closers := y] [scores := ys] _ second rest2 =>
    rewrite completionUnique _ x y first second, completionScoresUnique _ xs ys rest rest2 in rfl
  | Scored incomplete _ _, Skipped complete _ => Void.exfalso (complete incomplete)
  | Skipped complete _, Scored incomplete _ _ => Void.exfalso (complete incomplete)
  | Skipped _ rest, Skipped _ rest2 => completionScoresUnique _ a b rest rest2

--| An incomplete line has a score.
theorem scoredOfIncomplete ∀ (line: List Token) (incomplete: Incomplete line): exists (score: Nat) => autocompleteScore line = Some score :=
  match e: scan [] line with
    | Corrupted illegal => Void.exfalso (notCorruptedOfLegal line illegal (And.left incomplete) e)
    | Unclosed [] => Void.exfalso (And.right incomplete (scanBalanced line e))
    | Unclosed [top, ..below] => Witness (completionScore [top, ..below]) rfl

--| A list with an element `f` keeps has a nonempty `filterMap`.
theorem filterMapNotNil ∀ (f: a → Option b) (x: a) (y: b) (kept: f x = Some y) (xs: List a) (member: x ∈ xs): xs.filterMap f ≠ [] :=
  match xs, member with
    | [], member => empty => Void.exfalso member
    | [z, ..rest], Inl same => empty =>
      rewrite same, kept at empty in cases
    | [z, ..rest], Inr later => empty =>
      match f z with
        | None => filterMapNotNil f x y kept rest later empty

--| Part 2 is the middle completion score, for every list of lines with at
--| least one incomplete line.
theorem part2Correct ∀ (lines: List (List Token)) (line: List Token) (member: line ∈ lines) (incomplete: Incomplete line): Part2Answer lines (solvePart2 lines) :=
  match scoredOfIncomplete line incomplete with
    | Witness score scored =>
      Witness (lines.filterMap autocompleteScore)
        (Both (completionScoresCorrect lines) (middleIsMiddle (lines.filterMap autocompleteScore) (filterMapNotNil autocompleteScore line score scored lines member)))

--| With an odd number of incomplete lines, as the puzzle promises, the
--| spec's part 2 answer is unique: the program's is the only one.
theorem part2Unique ∀ (lines: List (List Token)) (a: Nat) (b: Nat) (odd: ∀ (scores: List Nat) => CompletionScores lines scores → scores.length % 2 = 1)
    (first: Part2Answer lines a) (second: Part2Answer lines b): a = b := match first with
      | Witness xs (Both scoredA middleA) =>
        match second with
          | Witness ys (Both scoredB middleB) =>
            let same := completionScoresUnique lines xs ys scoredA scoredB
            middleUnique xs a b (odd xs scoredA) middleA (rewrite same in middleB)
