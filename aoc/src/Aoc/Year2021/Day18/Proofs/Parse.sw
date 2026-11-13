--| The parser keeps the promise the answers' theorems assume: every number
--| it reads is reduced, so both answers' theorems hold of whatever
--| `parseNumbers` reads, with no hypothesis left.
-- (D2108)

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Aoc.Year2021.Day18.Spec (IsReduced, Part1, Part2, leaves)
import Std (Bool, Fail, List, Nat, Option, Result, Void)

--| A number `reduced` accepts, inside at most four pairs, has its leaves
--| inside at most four pairs and below 10.
theorem reducedLeaves (depth: Nat) (number: Number) (shallow: depth ≤ 4) (small: reduced depth number = True):
    List.All (leaf => leaf.depth ≤ 4 ∧ leaf.value ≤ 9) (leaves depth number) :=
  match number, small with
    | Regular value, small => Both (Both shallow omega) Trivial
    | Pair left right, ok =>
      let parts := ok.right
      List.allAppend _ (leaves (depth + 1) left) (leaves (depth + 1) right)
        (reducedLeaves (depth + 1) left (omega [ok.left]) parts.left)
        (reducedLeaves (depth + 1) right (omega [ok.left]) parts.right)

--| When `firstUnreduced` finds nothing, every number is reduced.
theorem findUnreducedNone (i: Nat) (numbers: List Number) (none: List.findIndexFrom i (x => not (reduced 0 x)) numbers = None): List.All IsReduced numbers :=
  match numbers with
    | [] => Trivial
    | [x, ..rest] =>
      match e: reduced 0 x with
        | True => Both (reducedLeaves 0 x omega e) (findUnreducedNone (Succ i) rest none)

--| `checkNumbers` passes its numbers on unchanged, and only if all are
--| reduced.
theorem checkNumbersOk (numbers: List Number) (checked: List Number) (h: Fail.toResult (() => checkNumbers numbers) = Ok checked): List.All IsReduced checked :=
  match e: firstUnreduced numbers with
    | None => rewrite <- Result.okInjective h in findUnreducedNone 0 numbers e

--| Whatever reads the numbers, `checkNumbers` passes on only reduced ones.
theorem checkedReduced (read: () → {Fail} List Number) (numbers: List Number) (parsed: Fail.toResult (() => checkNumbers (read ())) = Ok numbers):
    List.All IsReduced numbers :=
  let split := rewrite Fail.toResultThen read checkNumbers at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkNumbers x)) numbers split (u _ checked => checkNumbersOk u numbers checked)

--| The parser's guarantee: every number it reads is reduced.
theorem parseNumbersReduced (input: Text) (numbers: List Number) (parsed: Fail.toResult (() => parseNumbers input) = Ok numbers): List.All IsReduced numbers :=
  checkedReduced _ numbers parsed

--| Both answers from the input text: if `parseNumbers` reads `input` as
--| `numbers` and the program gives an answer (every sum it needs finishes
--| within its budget), the answer is the puzzle's.
theorem part1FromInput (input: Text) (numbers: List Number) (parsed: Fail.toResult (() => parseNumbers input) = Ok numbers) (answer: Nat)
    (solved: solvePart1 numbers = Some answer): Part1 numbers answer :=
  part1Correct numbers (parseNumbersReduced input numbers parsed) answer solved

theorem part2FromInput (input: Text) (numbers: List Number) (parsed: Fail.toResult (() => parseNumbers input) = Ok numbers) (answer: Nat)
    (solved: solvePart2 numbers = Some answer): Part2 numbers answer :=
  part2Correct numbers (parseNumbersReduced input numbers parsed) answer solved
