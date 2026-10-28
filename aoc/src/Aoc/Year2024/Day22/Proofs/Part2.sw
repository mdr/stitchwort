-- Part 2: the program's best total, over the sequences some buyer's prices
-- show, is the puzzle's most bananas over every sequence of four changes
-- from -9 to 9 (`part2Correct`). Every total is a possible sequence's
-- bananas (Keys.sw, Totals.sw), and a possible sequence with no total earns
-- nothing.

namespace Aoc.Year2024.Day22.Proofs
import Aoc.Year2024.Day22 (..)
import Aoc.Year2024.Day22.Spec (..)
import Std (Eq, List, Map, Nat, Option, Pair)

theorem getOrSome (totals: Map Changes Nat) (key: Changes) (value: Nat) (found: totals.get key = Some value): totals.getOr key 0 = value :=
  rewrite found in rfl

theorem getOrNone (totals: Map Changes Nat) (key: Changes) (missing: totals.get key = None): totals.getOr key 0 = 0 := rewrite missing in rfl

theorem leBoth (m: Nat) (n: Nat) (below: m ≤ n) (above: n ≤ m): m = n := omega

-- The best total is no more than the most bananas over any list holding
-- the changes of every five digits.
theorem bestTotalAtMost (possible: List Changes) (contains: HoldsDigitChanges possible) (count: Nat) (buyers: List Nat):
    bestTotal count buyers ≤ mostBananas possible count buyers :=
  let totals := bananasBySequence count buyers
  let most := (possible.map (bananas count buyers)).foldLeft 0 Nat.max
  match List.foldMaxMem totals.values 0 with
    | Inl zero => omega [zero]
    | Inr member =>
      List.anyElim _ (bestTotal count buyers ≤ most) totals.toList (List.memMapAny totals.toList Pair.snd (totals.values.foldLeft 0 Nat.max) member)
        (((key, value)) inList same =>
          let found := (Map.memToList totals key value).forward inList
          let earns: value = bananas count buyers key := Eq.trans (Eq.sym (getOrSome totals key value found)) (totalsBananas count buyers key)
          let bound :=
            List.leFoldMax (possible.map (bananas count buyers)) (bananas count buyers key) 0
              (List.memMap possible key (totalsKeysIn possible contains count buyers key value found) (bananas count buyers))
          omega [same, earns, bound])

-- And no less than the most bananas over any list of sequences.
theorem bestTotalAtLeast (possible: List Changes) (count: Nat) (buyers: List Nat):
    mostBananas possible count buyers ≤ bestTotal count buyers :=
  let totals := bananasBySequence count buyers
  let most := (possible.map (bananas count buyers)).foldLeft 0 Nat.max
  match List.foldMaxMem (possible.map (bananas count buyers)) 0 with
    | Inl zero => omega [zero]
    | Inr member =>
      List.anyElim _ (most ≤ bestTotal count buyers) possible (List.memMapAny possible (bananas count buyers) most member)
        (sequence inPossible same =>
          let earns := totalsBananas count buyers sequence
          match found: totals.get sequence with
            | Some value =>
              let bound :=
                List.leFoldMax totals.values value 0 (List.memMap totals.toList (sequence, value) ((Map.memToList totals sequence value).backward found) Pair.snd)
              omega [same, earns, getOrSome totals sequence value found, bound]
            | None => omega [same, earns, getOrNone totals sequence found])

-- Stated for any such list and only then for `possibleSequences`: a `≤`
-- about `possibleSequences` itself makes the checker fold all 130,321
-- sequences, and run out of stack.
theorem bestTotalAmong (possible: List Changes) (contains: HoldsDigitChanges possible) (count: Nat) (buyers: List Nat):
    bestTotal count buyers = mostBananas possible count buyers :=
  leBoth (bestTotal count buyers) (mostBananas possible count buyers) (bestTotalAtMost possible contains count buyers)
    (bestTotalAtLeast possible count buyers)

theorem bestTotalCorrect (count: Nat) (buyers: List Nat): bestTotal count buyers = mostBananas (sequencesOf possibleChanges) count buyers :=
  bestTotalAmong (sequencesOf possibleChanges) digitChangesPossible count buyers

theorem part2Correct (buyers: List Nat): solvePart2 buyers = mostBananas possibleSequences 2000 buyers := bestTotalCorrect 2000 buyers
