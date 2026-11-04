--| Day 3 proved, for every list of numbers: both answers are those of the
--| spec (Spec/), which looks each bit up by its position in every number.

namespace Aoc.Year2021.Day03.Proofs
import Aoc.Year2021.Day03 (..)
import Aoc.Year2021.Day03.Spec (..)
import Std (Eq, List, Nat, Option)

--| Columns. A column is a bit read off each number by `bitOf`, from the
--| numbers that have one.

--| Its 1s are the numbers whose bit is a 1.
theorem onesInColumn (bitOf: Bits → Option Bool): (numbers: List Bits) →
    List.count (List.filterMap numbers bitOf) (bit => bit) = List.count numbers (number => bitOf number == Some True)
  | [] => rfl
  | [number, ..rest] =>
    rewrite List.countCons rest number (number => bitOf number == Some True), <- onesInColumn bitOf rest in
      match bitOf number with
        | None => omega
        | Some bit => rewrite List.countCons (List.filterMap rest bitOf) bit (bit => bit) in cases

--| Its length is the numbers whose bit is a 1, and those whose bit is a 0.
theorem columnLength (bitOf: Bits → Option Bool): (numbers: List Bits) →
    List.length (List.filterMap numbers bitOf)
      = List.count numbers (number => bitOf number == Some True) + List.count numbers (number => bitOf number == Some False)
  | [] => rfl
  | [number, ..rest] =>
    rewrite List.countCons rest number (number => bitOf number == Some True),
      List.countCons rest number (number => bitOf number == Some False) in
      match bitOf number with
        | None => columnLength bitOf rest
        | Some bit => rewrite columnLength bitOf rest in cases

--| So the program's most common bit of a column is 1 when it has no more 0s
--| than 1s.
theorem mostCommonColumn (bitOf: Bits → Option Bool) (numbers: List Bits):
    mostCommon (List.filterMap numbers bitOf)
      = (List.count numbers (number => bitOf number == Some False) ≤ List.count numbers (number => bitOf number == Some True)) :=
  rewrite columnLength bitOf numbers, onesInColumn bitOf numbers in cases

--| The spec's most common bit at a position is the program's for the column
--| there.
theorem mostCommonAtColumn (numbers: List Bits) (position: Nat):
    mostCommonAt numbers position = mostCommon (List.filterMap numbers (number => List.get number position)) :=
  Eq.sym (mostCommonColumn (number => List.get number position) numbers)

--| The least common bit is the one the most common bit isn't, ties
--| included.
theorem leastIsNotMost (numbers: List Bits) (position: Nat): leastCommonAt numbers position = not (mostCommonAt numbers position) :=
  cases

-- Part 1.

--| The program's gamma rate's bits are the spec's.
theorem gammaBits (report: List Bits):
    List.map (List.transpose report) mostCommon = List.map (List.range (width report)) (mostCommonAt report) :=
  calc List.map (List.transpose report) mostCommon
    _ = List.map (List.map (List.range (width report)) (i => List.filterMap report (number => List.get number i))) mostCommon :=
      Eq.cong (cols => List.map cols mostCommon) (List.transposeColumns report)
    _ = List.map (List.range (width report)) (i => mostCommon (List.filterMap report (number => List.get number i))) := List.mapMap _ _ _
    _ = List.map (List.range (width report)) (mostCommonAt report) := List.mapCong _ _ _ (i => Eq.sym (mostCommonAtColumn report i))

--| And the epsilon rate's are them flipped.
theorem epsilonBits (report: List Bits):
    List.map (List.range (width report)) (leastCommonAt report) = List.map (List.map (List.range (width report)) (mostCommonAt report)) not :=
  Eq.trans (List.mapCong _ _ _ (i => leastIsNotMost report i)) (Eq.sym (List.mapMap _ _ _))

--| The epsilon rate is the gamma rate's bits flipped: the two add up to the
--| number with a 1 in every position, 2^width - 1.
theorem epsilonComplement (report: List Bits): gammaRate report + epsilonRate report + 1 = Nat.pow 2 (width report) :=
  let gamma := List.map (List.range (width report)) (mostCommonAt report)
  calc gammaRate report + epsilonRate report + 1
    _ = Nat.fromBits gamma + Nat.fromBits (List.map gamma not) + 1 := Eq.cong (e => Nat.fromBits gamma + Nat.fromBits e + 1) (epsilonBits report)
    _ = Nat.pow 2 (List.length gamma) := Nat.fromBitsFlipped gamma
    _ = Nat.pow 2 (width report) := rewrite List.lengthMap (List.range (width report)) (mostCommonAt report), List.lengthRangeFrom (width report) 0 in rfl

--| Part 1 is the puzzle's answer, for every list of numbers.
theorem part1Correct (report: List Bits): solvePart1 report = powerConsumption report :=
  let gamma := List.map (List.range (width report)) (mostCommonAt report)
  let flipped: Nat.pow 2 (List.length gamma) - 1 - Nat.fromBits gamma = Nat.fromBits (List.map gamma not) := omega [Nat.fromBitsFlipped gamma]
  calc solvePart1 report
    _ = Nat.fromBits gamma * (Nat.pow 2 (List.length gamma) - 1 - Nat.fromBits gamma) := rewrite gammaBits report in rfl
    _ = Nat.fromBits gamma * Nat.fromBits (List.map gamma not) := rewrite flipped in rfl
    _ = powerConsumption report := Eq.cong (e => Nat.fromBits gamma * Nat.fromBits e) (Eq.sym (epsilonBits report))

-- Part 2. The spec filters whole numbers by the bit at a position; the
-- program has dropped the bits before it, which every number left shares
-- (`prefix`).

--| The bit after a shared prefix is the first bit of the rest.
theorem getAfterPrefix (t: Bits): (prefix: Bits) → List.get (List.append prefix t) (List.length prefix) = List.head t
  | [] => cases
  | [first, ..rest] => getAfterPrefix t rest

--| Keeping the numbers with `bit` after the prefix is keeping the rests that
--| start with it, without it.
theorem keepAfterPrefix (prefix: Bits) (bit: Bool): (rests: List Bits) →
    keep (List.map rests (rest => List.append prefix rest)) (List.length prefix) bit
      = List.map (List.filterMap rests (afterBit bit)) (rest => List.append prefix [bit, ..rest])
  | [] => rfl
  | [rest, ..others] =>
    rewrite getAfterPrefix rest prefix, keepAfterPrefix prefix bit others in cases

--| The bit kept moves onto the prefix.
theorem growPrefix (prefix: Bits) (bit: Bool) (rests: List Bits):
    List.map rests (rest => List.append prefix [bit, ..rest]) = List.map rests (rest => List.append (List.append prefix [bit]) rest) :=
  List.mapCong _ _ _ (rest => Eq.sym (List.appendAssoc prefix [bit] rest))

--| How many numbers have `bit` after the prefix: the rests that start with it.
theorem howManyAfterPrefix (prefix: Bits) (rests: List Bits) (bit: Bool):
    howMany (List.map rests (rest => List.append prefix rest)) (List.length prefix) bit
      = List.count rests (rest => List.head rest == Some bit) :=
  rewrite List.countMap _ _ _, getAfterPrefix _ prefix in rfl

--| The two criteria pick the same bits as the program's.
theorem mostCommonAfterPrefix (prefix: Bits) (rests: List Bits):
    mostCommonAt (List.map rests (rest => List.append prefix rest)) (List.length prefix) = mostCommon (List.filterMap rests List.head) :=
  rewrite howManyAfterPrefix prefix rests False, howManyAfterPrefix prefix rests True in Eq.sym (mostCommonColumn List.head rests)

theorem leastCommonAfterPrefix (prefix: Bits) (rests: List Bits):
    leastCommonAt (List.map rests (rest => List.append prefix rest)) (List.length prefix)
      = not (mostCommon (List.filterMap rests List.head)) :=
  rewrite leastIsNotMost _ _, mostCommonAfterPrefix prefix rests in rfl

--| One step of the filtering, with the steps after it (`later`) done: the
--| spec keeps the numbers whose next bit is the chosen one, which the program
--| finds as the rests that start with it, and the prefix grows by it.
theorem ratingStep (choose: List Bool → Bool) (criterion: List Bits → Nat → Bool)
    (agree: (prefix: Bits) → (rests: List Bits) →
      criterion (List.map rests (rest => List.append prefix rest)) (List.length prefix) = choose (List.filterMap rests List.head))
    (k: Nat) (prefix: Bits) (rests: List Bits)
    (later: (prefix: Bits) → (rests: List Bits) →
      findRating criterion (List.map rests (rest => List.append prefix rest)) (List.rangeFrom k (List.length prefix))
        = Option.map (rating choose k rests) (rest => List.append prefix rest)):
    findRating criterion
        (keep (List.map rests (rest => List.append prefix rest)) (List.length prefix)
          (criterion (List.map rests (rest => List.append prefix rest)) (List.length prefix)))
        (List.rangeFrom k (Succ (List.length prefix)))
      = Option.map
        (Option.map (rating choose k (List.filterMap rests (afterBit (choose (List.filterMap rests List.head)))))
          (Cons (choose (List.filterMap rests List.head))))
        (rest => List.append prefix rest) :=
  let bit := choose (List.filterMap rests List.head)
  let kept := List.filterMap rests (afterBit bit)
  calc findRating criterion
      (keep (List.map rests (rest => List.append prefix rest)) (List.length prefix)
        (criterion (List.map rests (rest => List.append prefix rest)) (List.length prefix)))
      (List.rangeFrom k (Succ (List.length prefix)))
    _ = findRating criterion (List.map kept (rest => List.append prefix [bit, ..rest])) (List.rangeFrom k (Succ (List.length prefix))) :=
      rewrite agree prefix rests, keepAfterPrefix prefix bit rests in rfl
    _ = findRating criterion (List.map kept (rest => List.append (List.append prefix [bit]) rest))
        (List.rangeFrom k (List.length (List.append prefix [bit]))) :=
      rewrite growPrefix prefix bit kept, List.lengthSnoc prefix bit in rfl
    _ = Option.map (rating choose k kept) (rest => List.append (List.append prefix [bit]) rest) := later (List.append prefix [bit]) kept
    _ = Option.map (rating choose k kept) (rest => List.append prefix [bit, ..rest]) :=
      Option.mapCong _ _ _ (rest => List.appendAssoc prefix [bit] rest)
    _ = Option.map (Option.map (rating choose k kept) (Cons bit)) (rest => List.append prefix rest) := Eq.sym (Option.mapMap _ _ _)

--| The spec's filtering, from the numbers that share a prefix, finds the
--| program's rating of their rests, after the prefix; for any criterion that
--| picks the bit the program's `choose` picks.
theorem ratingAfterPrefix (choose: List Bool → Bool) (criterion: List Bits → Nat → Bool)
    (agree: (prefix: Bits) → (rests: List Bits) →
      criterion (List.map rests (rest => List.append prefix rest)) (List.length prefix) = choose (List.filterMap rests List.head)):
    (k: Nat) → (prefix: Bits) → (rests: List Bits) →
    findRating criterion (List.map rests (rest => List.append prefix rest)) (List.rangeFrom k (List.length prefix))
      = Option.map (rating choose k rests) (rest => List.append prefix rest)
  | k, prefix, [rest] => rfl
  | Zero, prefix, [] => rfl
  | Zero, prefix, [first, second, ..others] => rfl
  | Succ k, prefix, [] => ratingStep choose criterion agree k prefix [] (ratingAfterPrefix choose criterion agree k)
  | Succ k, prefix, [first, second, ..others] =>
    ratingStep choose criterion agree k prefix [first, second, ..others] (ratingAfterPrefix choose criterion agree k)

--| From the whole report.
theorem ratingCorrect (choose: List Bool → Bool) (criterion: List Bits → Nat → Bool)
    (agree: (prefix: Bits) → (rests: List Bits) →
      criterion (List.map rests (rest => List.append prefix rest)) (List.length prefix) = choose (List.filterMap rests List.head))
    (report: List Bits):
    findRating criterion report (List.range (width report)) = rating choose (width report) report :=
  calc findRating criterion report (List.range (width report))
    _ = findRating criterion (List.map report (rest => rest)) (List.range (width report)) :=
      Eq.cong (numbers => findRating criterion numbers (List.range (width report))) (Eq.sym (List.mapId report))
    _ = Option.map (rating choose (width report) report) (rest => rest) := ratingAfterPrefix choose criterion agree (width report) [] report
    _ = rating choose (width report) report := Option.mapId _

--| Part 2 is the puzzle's answer, for every list of numbers: the same
--| number, or no number on both sides.
theorem part2Correct (report: List Bits): solvePart2 report = lifeSupportRating report :=
  rewrite ratingCorrect mostCommon mostCommonAt mostCommonAfterPrefix report,
    ratingCorrect (column => not (mostCommon column)) leastCommonAt leastCommonAfterPrefix report in cases
