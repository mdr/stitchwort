-- The program's list of element counts has the same members as the
-- puzzle's (`quantitiesInto`, `quantitiesBack`), so the same greatest and
-- least (`maximumSame`, `minimumSame`), and the answer is the puzzle's for
-- every number of steps (`spreadAfterCorrect`).

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Aoc.Year2021.Day14.Spec (..)
import Std (Bool, DecEq, Eq, Exists, Iff, List, Map, Nat, Option, Ord, Void)

-- Membership and counting.

-- A member is counted at least once...
theorem countPositive [auto eq: DecEq a] (c: a) (xs: List a) (member: c ∈ xs): 0 < List.count xs (== c) :=
  omega [List.countFalse xs, List.countLtMem xs (x => False) (== c) (x _ never => cases) c member (DecEq.refl c) rfl]

-- ...and an element counted is a member.
theorem positiveMember [auto eq: DecEq a] (c: a): (xs: List a) → 0 < List.count xs (== c) → c ∈ xs
  | Nil, positive => omega
  | Cons x rest, positive =>
    match t: x == c with
      | True => Inl (DecEq.sound x c t)
      | False => Inr (positiveMember c rest (omega [List.countCons rest x (== c)]))

-- A sum with a positive term has a member that gives it.
theorem sumByPositive (f: a → Nat): (xs: List a) → 0 < List.sumBy xs f → ∃ (x: a) => x ∈ xs ∧ 0 < f x
  | Nil, positive => Void.exfalso omega
  | Cons x rest, positive =>
    match Nat.decLessThan 0 (f x) with
      | Yes h => Witness x (Both (Inl rfl) h)
      | No h =>
        match sumByPositive f rest (omega [List.sumByCons rest x f]) with
          | Witness y (Both member gives) => Witness y (Both (Inr member) gives)

-- An element after the first ends a pair.
theorem memAfterFirst (c: Char) (a: Char): (rest: List Char) → c ∈ rest → ∃ (pair: (Char, Char)) => pair ∈ List.zipWithNext (Cons a rest) ∧ pair.snd = c
  | Nil, member => Void.exfalso member
  | Cons b more, Inl same => Witness (a, b) (Both (Inl rfl) same)
  | Cons b more, Inr member =>
    match memAfterFirst c b more member with
      | Witness pair (Both inPairs ends) => Witness pair (Both (Inr inPairs) ends)

-- A pair of the polymer has a count in the counts that stand for it.
theorem pairCounted (counts: PairCounts) (polymer: List Char) (represents: Represents counts polymer) (pair: (Char, Char)) (member: pair ∈ List.zipWithNext polymer):
    pair ∈ Map.keys counts :=
  let counted := countPositive pair (List.zipWithNext polymer) member
  let asSum := List.countSumBy (List.zipWithNext polymer) (== pair)
  let weighted := represents (other => Bool.toNat (other == pair))
  match sumByPositive ((entry: ((Char, Char), Nat)) => entry.snd * Bool.toNat (entry.fst == pair)) (Map.toList counts) (omega [counted, asSum, weighted]) with
    | Witness entry (Both inCounts gives) =>
      match t: entry.fst == pair with
        | True => rewrite <- DecEq.sound entry.fst pair t in List.memMap (Map.toList counts) entry inCounts Pair.fst
        | False => Void.exfalso omega

-- The two lists of element counts.

-- The counts the program looks at, for a polymer starting with `first`.
def programQuantities (first: Char) (counts: PairCounts): List Nat :=
  Cons first (counts.keys.map Pair.snd) |> .distinct |> .map (elementCount first counts) |> .filter (quantity => 0 < quantity)

-- The puzzle's: each element's count, once per element.
def puzzleQuantities (polymer: List Char): List Nat := polymer.distinct.map (quantity polymer)

theorem quantitiesInto (first: Char) (tail: List Char) (counts: PairCounts) (represents: Represents counts (Cons first tail)) (v: Nat)
    (member: v ∈ programQuantities first counts): v ∈ puzzleQuantities (Cons first tail) :=
  let candidates := List.distinct (Cons first (List.map (Map.keys counts) Pair.snd))
  let (Both inMapped positive) := List.memFilter (List.map candidates (elementCount first counts)) (quantity => 0 < quantity) v member
  match List.memMapElim (elementCount first counts) v candidates inMapped with
    | Witness c (Both _ same) =>
      let equal := elementCountQuantity first tail counts represents c
      let counted: 0 < List.count (Cons first tail) (== c) := omega [equal, same, positive]
      let inPolymer := positiveMember c (Cons first tail) counted
      let inDistinct := (List.memDistinct c (Cons first tail)).backward inPolymer
      rewrite <- same, equal in List.memMap (List.distinct (Cons first tail)) c inDistinct (quantity (Cons first tail))

theorem quantitiesBack (first: Char) (tail: List Char) (counts: PairCounts) (represents: Represents counts (Cons first tail)) (v: Nat)
    (member: v ∈ puzzleQuantities (Cons first tail)): v ∈ programQuantities first counts :=
  let polymer := Cons first tail
  let keyEnds := List.map (Map.keys counts) Pair.snd
  match List.memMapElim (quantity polymer) v (List.distinct polymer) member with
    | Witness c (Both inDistinct same) =>
      let inPolymer := (List.memDistinct c polymer).forward inDistinct
      let candidate: c ∈ Cons first keyEnds :=
        match inPolymer with
          | Inl isFirst => Inl isFirst
          | Inr inTail =>
            match memAfterFirst c first tail inTail with
              | Witness pair (Both inPairs ends) =>
                Inr (rewrite <- ends in List.memMap (Map.keys counts) pair (pairCounted counts polymer represents pair inPairs) Pair.snd)
      let inCandidates := (List.memDistinct c (Cons first keyEnds)).backward candidate
      let equal := elementCountQuantity first tail counts represents c
      let positive := countPositive c polymer inPolymer
      List.memFilterIntro (List.map (List.distinct (Cons first keyEnds)) (elementCount first counts)) (quantity => 0 < quantity) v
        (rewrite <- same, <- equal in List.memMap (List.distinct (Cons first keyEnds)) c inCandidates (elementCount first counts))
        (cases)

-- The program's answer from counts that stand for a polymer is the
-- puzzle's answer for that polymer.
theorem spreadCorrect (first: Char) (rest: List Char) (tail: List Char) (counts: PairCounts) (represents: Represents counts (Cons first tail)):
    spread (Cons first rest) counts = spreadOf (Cons first tail) :=
  let into := quantitiesInto first tail counts represents
  let back := quantitiesBack first tail counts represents
  rewrite maximumSame (programQuantities first counts) (puzzleQuantities (Cons first tail)) into back,
    minimumSame (programQuantities first counts) (puzzleQuantities (Cons first tail)) into back in rfl

-- The answer is the puzzle's after any number of steps, if no two rules
-- are for the same pair.
theorem spreadAfterCorrect (steps: Nat) (manual: Manual) (one: OneRulePerPair manual.rules): spreadAfter steps manual = answer steps manual :=
  match manual with
    | { template = Nil, rules } => rewrite stepsEmpty rules steps in rfl
    | { template = Cons first rest, rules } =>
      let start := { template = Cons first rest, rules }
      let counts := Nat.iterate steps (stepCounts (ruleTable rules)) (countPairs (Cons first rest))
      let represents := iterateRepresents start one steps (countPairs (Cons first rest)) (Cons first rest) (countPairsRepresents (Cons first rest))
      match stepsKeepFirst rules steps first rest with
        | Witness tail e =>
          let ended: Represents counts (Cons first tail) := rewrite e at represents in represents
          calc spreadAfter steps start
            _ = spread (Cons first rest) counts
            _ = spreadOf (Cons first tail) := spreadCorrect first rest tail counts ended
            _ = answer steps start := Eq.sym (Eq.cong spreadOf e)

-- Part 1 is the puzzle's answer after 10 steps, part 2 after 40, for every
-- manual whose rules give each pair at most one insertion.
theorem part1Correct (manual: Manual) (one: OneRulePerPair manual.rules): solvePart1 manual = answer 10 manual := spreadAfterCorrect 10 manual one

theorem part2Correct (manual: Manual) (one: OneRulePerPair manual.rules): solvePart2 manual = answer 40 manual := spreadAfterCorrect 40 manual one
