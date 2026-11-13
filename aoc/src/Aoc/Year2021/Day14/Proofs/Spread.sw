--| The program's list of element counts has the same members as the
--| puzzle's (`quantitiesInto`, `quantitiesBack`), so the same greatest and
--| least (std's `List.maximumSameMembers`, `List.minimumSameMembers`), and
--| the answer is the puzzle's for every number of steps
--| (`spreadAfterCorrect`).

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Aoc.Year2021.Day14.Spec (..)
import Std (Bool, DecEq, Eq, Exists, Iff, List, Map, Nat, Option, Ord, Void)

--| A sum with a positive term has a member that gives it.
theorem sumByPositive (f: a → Nat) (xs: List a) (positive: 0 < xs.sumBy f): ∃ (x: a) => x ∈ xs ∧ 0 < f x :=
  match xs with
    | [x, ..rest] =>
      if h: 0 < f x then Witness x (Both (Inl rfl) h)
      else
        match sumByPositive f rest (omega [List.sumByCons rest x f]) with
          | Witness y (Both member gives) => Witness y (Both (Inr member) gives)

--| An element after the first ends a pair.
theorem memAfterFirst (c: Char) (a: Char) (rest: List Char) (h: c ∈ rest): ∃ (pair: ElementPair) => pair ∈ pairsOf [a, ..rest] ∧ pair.second = c :=
  match rest, h with
    | [], member => Void.exfalso member
    | [b, ..more], Inl same => Witness ({ first = a, second = b }) (Both (Inl rfl) same)
    | [b, ..more], Inr member =>
      match memAfterFirst c b more member with
        | Witness pair (Both inPairs ends) => Witness pair (Both (Inr inPairs) ends)

--| A pair of the polymer has a count in the counts that stand for it.
theorem pairCounted (counts: PairCounts) (polymer: List Char) (represents: Represents counts polymer) (pair: ElementPair) (member: pair ∈ pairsOf polymer):
    pair ∈ counts.keys :=
  let counted := List.countPositive (pairsOf polymer) (== pair) pair member (DecEq.refl pair)
  let asSum := List.countSumBy (pairsOf polymer) (== pair)
  let weighted := represents (other => Bool.toNat (other == pair))
  match sumByPositive ((entry: (ElementPair, Nat)) => entry.snd * Bool.toNat (entry.fst == pair)) (Map.toList counts) (omega [counted, asSum, weighted]) with
    | Witness entry (Both inCounts gives) =>
      match t: entry.fst == pair with
        | True => rewrite <- t.read in List.memMap (Map.toList counts) entry inCounts Pair.fst
        | False => Void.exfalso omega

-- The two lists of element counts.

--| The counts the program looks at, for a polymer starting with `first`.
def programQuantities (first: Char) (counts: PairCounts): List Nat :=
  [first, ..counts.keys.map ElementPair.second] |> .unique |> .map (elementCount first counts) |> .filter (quantity => 0 < quantity)

--| The puzzle's: each element's count, once per element.
def puzzleQuantities (polymer: List Char): List Nat := polymer.unique.map (quantity polymer)

theorem quantitiesInto (first: Char) (tail: List Char) (counts: PairCounts) (represents: Represents counts [first, ..tail]) (v: Nat)
    (member: v ∈ programQuantities first counts): v ∈ puzzleQuantities [first, ..tail] :=
  let candidates := List.unique [first, ..List.map (Map.keys counts) ElementPair.second]
  let (Both inMapped positive) := List.memFilter (List.map candidates (elementCount first counts)) (quantity => 0 < quantity) member
  match List.memMapElim (elementCount first counts) v candidates inMapped with
    | Witness c (Both _ same) =>
      let equal := elementCountQuantity first tail counts represents c
      let counted: 0 < List.count [first, ..tail] (== c) := omega [equal, same, positive]
      let inPolymer := List.memOfCountPositive c [first, ..tail] counted
      let inDistinct := (List.memUnique c [first, ..tail]).backward inPolymer
      rewrite <- same, equal in List.memMap (List.unique [first, ..tail]) c inDistinct (quantity [first, ..tail])

theorem quantitiesBack (first: Char) (tail: List Char) (counts: PairCounts) (represents: Represents counts [first, ..tail]) (v: Nat)
    (member: v ∈ puzzleQuantities [first, ..tail]): v ∈ programQuantities first counts :=
  let polymer := [first, ..tail]
  let keyEnds := List.map (Map.keys counts) ElementPair.second
  match List.memMapElim (quantity polymer) v (List.unique polymer) member with
    | Witness c (Both inDistinct same) =>
      let inPolymer := (List.memUnique c polymer).forward inDistinct
      let candidate: c ∈ [first, ..keyEnds] :=
        match inPolymer with
          | Inl isFirst => Inl isFirst
          | Inr inTail =>
            match memAfterFirst c first tail inTail with
              | Witness pair (Both inPairs ends) =>
                Inr (rewrite <- ends in List.memMap (Map.keys counts) pair (pairCounted counts polymer represents pair inPairs) ElementPair.second)
      let inCandidates := (List.memUnique c [first, ..keyEnds]).backward candidate
      let equal := elementCountQuantity first tail counts represents c
      let positive := List.countPositive polymer (== c) c inPolymer (DecEq.refl c)
      List.memFilterIntro (List.map (List.unique [first, ..keyEnds]) (elementCount first counts)) (quantity => 0 < quantity)
        (rewrite <- same, <- equal in List.memMap (List.unique [first, ..keyEnds]) c inCandidates (elementCount first counts))
        (cases)

--| The program's answer from counts that stand for a polymer is the
--| puzzle's answer for that polymer.
theorem spreadCorrect (first: Char) (rest: List Char) (tail: List Char) (counts: PairCounts) (represents: Represents counts [first, ..tail]):
    spread [first, ..rest] counts = spreadOf [first, ..tail] :=
  let into := quantitiesInto first tail counts represents
  let back := quantitiesBack first tail counts represents
  rewrite List.maximumSameMembers (programQuantities first counts) (puzzleQuantities [first, ..tail]) into back,
    List.minimumSameMembers (programQuantities first counts) (puzzleQuantities [first, ..tail]) into back in rfl

--| The answer is the puzzle's after any number of steps, if no two rules
--| are for the same pair.
theorem spreadAfterCorrect (steps: Nat) (manual: Manual) (one: OneRulePerPair manual.rules): spreadAfter steps manual = answer steps manual :=
  match manual with
    | { template = [], rules } => rewrite stepsEmpty rules steps in rfl
    | { template = [first, ..rest], rules } =>
      let start := { template = [first, ..rest], rules }
      let counts := Nat.iterate steps (stepCounts (ruleTable rules)) (countPairs [first, ..rest])
      let represents := iterateRepresents start one steps (countPairs [first, ..rest]) [first, ..rest] (countPairsRepresents [first, ..rest])
      match stepsKeepFirst rules steps first rest with
        | Witness tail e =>
          let ended: Represents counts [first, ..tail] := rewrite e at represents in represents
          calc spreadAfter steps start
            _ = spread [first, ..rest] counts
            _ = spreadOf [first, ..tail] := spreadCorrect first rest tail counts ended
            _ = answer steps start := Eq.sym (Eq.cong spreadOf e)

--| Part 1 is the puzzle's answer after 10 steps, part 2 after 40, for every
--| manual whose rules give each pair at most one insertion.
theorem part1Correct (manual: Manual) (one: OneRulePerPair manual.rules): solvePart1 manual = answer 10 manual := spreadAfterCorrect 10 manual one

theorem part2Correct (manual: Manual) (one: OneRulePerPair manual.rules): solvePart2 manual = answer 40 manual := spreadAfterCorrect 40 manual one
