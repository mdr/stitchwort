--| Day 3 proved, for every list of numbers: both answers are those of the
--| spec (Spec/), which looks each bit up by its position in every number.

namespace Aoc.Year2021.Day03.Proofs
import Aoc.Common (Bits)
import Aoc.Common.Proofs (..)
import Aoc.Year2021.Day03 (..)
import Aoc.Year2021.Day03.Spec (..)
import Std (Eq, List, Nat, Option)

--| Columns. A column is a bit read off each number by `bitOf`, from the
--| numbers that have one.

--| Its 1s are the numbers whose bit is a 1.
theorem onesInColumn (bitOf: Bits → Option Bool) (numbers: List Bits):
    (numbers.filterMap bitOf).count (bit => bit) = numbers.count (number => bitOf number == Some True) :=
  match numbers with
    | [] => rfl
    | [number, ..rest] =>
      rewrite List.countCons rest number (number => bitOf number == Some True), <- onesInColumn bitOf rest in
        match bitOf number with
          | None => omega
          | Some bit => rewrite List.countCons (List.filterMap rest bitOf) bit (bit => bit) in cases

--| So the program's most common bit of a column is 1 when it has no more 0s
--| than 1s.
theorem mostCommonColumn (bitOf: Bits → Option Bool) (numbers: List Bits):
    mostCommon (numbers.filterMap bitOf)
      = (numbers.count (number => bitOf number == Some False) ≤ numbers.count (number => bitOf number == Some True)) :=
  rewrite List.lengthFilterMapBool bitOf numbers, onesInColumn bitOf numbers in cases

--| The spec's most common bit at a position is the program's for the column
--| there.
theorem mostCommonAtColumn (numbers: List Bits) (position: Nat):
    mostCommonAt numbers position = mostCommon (numbers.filterMap (number => Bits.get number position)) :=
  Eq.sym (mostCommonColumn (number => Bits.get number position) numbers)

--| The least common bit is the one the most common bit isn't, ties
--| included.
theorem leastIsNotMost (numbers: List Bits) (position: Nat): leastCommonAt numbers position = not (mostCommonAt numbers position) :=
  cases

-- Part 1.

--| The program's columns, read from the numbers' bits, are the spec's: the
--| bits at each position of the first number's width.
theorem columns (report: List Bits):
    (report.map Bits.bits).transpose
      = (List.range 0 (width report)).map (i => report.filterMap (number => Bits.get number i)) :=
  let first: List.length (List.headOr (List.map report Bits.bits) []) = width report :=
    match report with
      | [] => rfl
      | [number, ..others] => rfl
  calc List.transpose (List.map report Bits.bits)
    _ = List.map (List.range 0 (List.length (List.headOr (List.map report Bits.bits) [])))
      (i => List.filterMap (List.map report Bits.bits) (row => List.get row i)) := List.transposeColumns _
    _ = List.map (List.range 0 (width report)) (i => List.filterMap report (number => Bits.get number i)) :=
      rewrite first, List.filterMapMap in rfl

--| The program's gamma rate's bits are the spec's.
theorem gammaBits (report: List Bits):
    (report.map Bits.bits).transpose.map mostCommon = (List.range 0 (width report)).map (mostCommonAt report) :=
  calc List.map (List.transpose (List.map report Bits.bits)) mostCommon
    _ = List.map (List.map (List.range 0 (width report)) (i => List.filterMap report (number => Bits.get number i))) mostCommon :=
      Eq.cong (cols => List.map cols mostCommon) (columns report)
    _ = List.map (List.range 0 (width report)) (i => mostCommon (List.filterMap report (number => Bits.get number i))) := List.mapMap _ _ _
    _ = List.map (List.range 0 (width report)) (mostCommonAt report) := List.mapCong _ _ _ (i => Eq.sym (mostCommonAtColumn report i))

--| And the epsilon rate's are them flipped.
theorem epsilonBits (report: List Bits):
    epsilon report = Bits.complement (gamma report) :=
  Eq.cong (bits => { bits }) (Eq.trans (List.mapCong _ _ _ (i => leastIsNotMost report i)) (Eq.sym (List.mapMap _ _ _)))

--| The epsilon rate is the gamma rate's bits flipped: the two add up to the
--| number with a 1 in every position, 2^width - 1.
theorem epsilonComplement (report: List Bits): gammaRate report + epsilonRate report + 1 = Nat.pow 2 (width report) :=
  calc gammaRate report + epsilonRate report + 1
    _ = (gamma report).value + (Bits.complement (gamma report)).value + 1 := Eq.cong (e => (gamma report).value + e.value + 1) (epsilonBits report)
    _ = Nat.pow 2 (gamma report).width := Bits.complementValue (gamma report)
    _ = Nat.pow 2 (width report) := rewrite List.lengthMap (List.range 0 (width report)) (mostCommonAt report), List.lengthRangeFrom (width report) 0 in rfl

--| Part 1 is the puzzle's answer, for every list of numbers.
theorem part1Correct (report: List Bits): solvePart1 report = powerConsumption report :=
  let ours: Bits := { bits = List.map (List.transpose (List.map report Bits.bits)) mostCommon }
  let sameGamma: ours = gamma report := Eq.cong (bits => { bits }) (gammaBits report)
  calc solvePart1 report
    _ = ours.value * ours.complement.value := rfl
    _ = (gamma report).value * (Bits.complement (gamma report)).value := Eq.cong (g => g.value * g.complement.value) sameGamma
    _ = powerConsumption report := Eq.cong (e => (gamma report).value * Bits.value e) (Eq.sym (epsilonBits report))

-- Part 2. The spec filters whole numbers by the bit at a position; the
-- program has dropped the bits before it, which every number left shares
-- (`prefix`).

--| The bit after a shared prefix is the first bit of the rest.
theorem getAfterPrefix (t: Bits) (prefix: Bits): Bits.get (Bits.append prefix t) prefix.width = Bits.first t :=
  Bits.getAppendWidth t prefix

--| Keeping the numbers with `bit` after the prefix is keeping the rests that
--| start with it, without it.
theorem keepAfterPrefix (prefix: Bits) (bit: Bool) (rests: List Bits): keep (rests.map (rest => Bits.append prefix rest)) (Bits.width prefix) bit
    = (rests.filterMap (rest => Bits.afterBit rest bit)).map (rest => Bits.append prefix (Bits.cons rest bit)) :=
  match rests with
    | [] => rfl
    | [{ bits }, ..others] =>
      rewrite getAfterPrefix { bits } prefix, keepAfterPrefix prefix bit others in cases

--| The bit kept moves onto the prefix.
theorem growPrefix (prefix: Bits) (bit: Bool) (rests: List Bits):
    rests.map (rest => Bits.append prefix (Bits.cons rest bit)) = rests.map (rest => Bits.append (Bits.append prefix (Bits.cons Bits.empty bit)) rest) :=
  List.mapCong _ _ _ (rest => Eq.sym (Bits.appendAssoc prefix (Bits.cons Bits.empty bit) rest))

--| How many numbers have `bit` after the prefix: the rests that start with it.
theorem howManyAfterPrefix (prefix: Bits) (rests: List Bits) (bit: Bool):
    howMany (rests.map (rest => Bits.append prefix rest)) (Bits.width prefix) bit
      = rests.count (rest => Bits.first rest == Some bit) :=
  rewrite List.countMap _ _ _, getAfterPrefix _ prefix in rfl

--| The two criteria pick the same bits as the program's.
theorem mostCommonAfterPrefix (prefix: Bits) (rests: List Bits):
    mostCommonAt (rests.map (rest => Bits.append prefix rest)) (Bits.width prefix) = mostCommon (rests.filterMap Bits.first) :=
  rewrite howManyAfterPrefix prefix rests False, howManyAfterPrefix prefix rests True in Eq.sym (mostCommonColumn Bits.first rests)

theorem leastCommonAfterPrefix (prefix: Bits) (rests: List Bits):
    leastCommonAt (rests.map (rest => Bits.append prefix rest)) (Bits.width prefix)
      = not (mostCommon (rests.filterMap Bits.first)) :=
  rewrite leastIsNotMost _ _, mostCommonAfterPrefix prefix rests in rfl

--| One step of the filtering, with the steps after it (`later`) done: the
--| spec keeps the numbers whose next bit is the chosen one, which the program
--| finds as the rests that start with it, and the prefix grows by it.
theorem ratingStep (choose: List Bool → Bool) (criterion: List Bits → Nat → Bool)
    (agree: ∀ (prefix: Bits) (rests: List Bits) =>
      criterion (rests.map (rest => Bits.append prefix rest)) (Bits.width prefix) = choose (rests.filterMap Bits.first))
    (k: Nat) (prefix: Bits) (rests: List Bits)
    (later: ∀ (prefix: Bits) (rests: List Bits) =>
      findRating criterion (rests.map (rest => Bits.append prefix rest)) (List.rangeFrom k (Bits.width prefix))
        = Option.map (rating choose k rests) (rest => Bits.append prefix rest)):
    findRating criterion
        (keep (rests.map (rest => Bits.append prefix rest)) (Bits.width prefix)
          (criterion (rests.map (rest => Bits.append prefix rest)) (Bits.width prefix)))
        (List.rangeFrom k (Succ (Bits.width prefix)))
      = Option.map
        ((rating choose k (rests.filterMap (rest => Bits.afterBit rest (choose (rests.filterMap Bits.first))))).map
          (rest => Bits.cons rest (choose (rests.filterMap Bits.first))))
        (rest => Bits.append prefix rest) :=
  let bit := choose (List.filterMap rests Bits.first)
  let kept := List.filterMap rests (rest => Bits.afterBit rest bit)
  calc findRating criterion
      (keep (List.map rests (rest => Bits.append prefix rest)) (Bits.width prefix)
        (criterion (List.map rests (rest => Bits.append prefix rest)) (Bits.width prefix)))
      (List.rangeFrom k (Succ (Bits.width prefix)))
    _ = findRating criterion (List.map kept (rest => Bits.append prefix (Bits.cons rest bit))) (List.rangeFrom k (Succ (Bits.width prefix))) :=
      rewrite agree prefix rests, keepAfterPrefix prefix bit rests in rfl
    _ = findRating criterion (List.map kept (rest => Bits.append (Bits.append prefix (Bits.cons Bits.empty bit)) rest))
        (List.rangeFrom k (Bits.width (Bits.append prefix (Bits.cons Bits.empty bit)))) :=
      rewrite growPrefix prefix bit kept, Bits.widthAppendBit prefix bit in rfl
    _ = Option.map (rating choose k kept) (rest => Bits.append (Bits.append prefix (Bits.cons Bits.empty bit)) rest) := later (Bits.append prefix (Bits.cons Bits.empty bit)) kept
    _ = Option.map (rating choose k kept) (rest => Bits.append prefix (Bits.cons rest bit)) :=
      Option.mapCong _ _ _ (rest => Bits.appendAssoc prefix (Bits.cons Bits.empty bit) rest)
    _ = Option.map (Option.map (rating choose k kept) (rest => Bits.cons rest bit)) (rest => Bits.append prefix rest) := Eq.sym (Option.mapMap _ _ _)

--| The spec's filtering, from the numbers that share a prefix, finds the
--| program's rating of their rests, after the prefix; for any criterion that
--| picks the bit the program's `choose` picks.
theorem ratingAfterPrefix (choose: List Bool → Bool) (criterion: List Bits → Nat → Bool)
    (agree: ∀ (prefix: Bits) (rests: List Bits) =>
      criterion (rests.map (rest => Bits.append prefix rest)) (Bits.width prefix) = choose (rests.filterMap Bits.first))
    (k: Nat) (prefix: Bits) (rests: List Bits): findRating criterion (rests.map (rest => Bits.append prefix rest)) (List.rangeFrom k (Bits.width prefix))
    = Option.map (rating choose k rests) (rest => Bits.append prefix rest) := match k, rests with
      | k, [rest] => rfl
      | Zero, [] => rfl
      | Zero, [first, second, ..others] => rfl
      | Succ k, [] => ratingStep choose criterion agree k prefix [] (ratingAfterPrefix choose criterion agree k)
      | Succ k, [first, second, ..others] =>
        ratingStep choose criterion agree k prefix [first, second, ..others] (ratingAfterPrefix choose criterion agree k)

--| From the whole report.
theorem ratingCorrect (choose: List Bool → Bool) (criterion: List Bits → Nat → Bool)
    (agree: ∀ (prefix: Bits) (rests: List Bits) =>
      criterion (rests.map (rest => Bits.append prefix rest)) (Bits.width prefix) = choose (rests.filterMap Bits.first))
    (report: List Bits):
    findRating criterion report (List.range 0 (width report)) = rating choose (width report) report :=
  let unprefixed: List.map report (rest => Bits.append Bits.empty rest) = report :=
    Eq.trans (List.mapCong _ _ _ (rest => Bits.emptyAppend rest)) (List.mapId report)
  calc findRating criterion report (List.range 0 (width report))
    _ = findRating criterion (List.map report (rest => Bits.append Bits.empty rest)) (List.rangeFrom (width report) (Bits.width Bits.empty)) :=
      rewrite unprefixed in rfl
    _ = Option.map (rating choose (width report) report) (rest => Bits.append Bits.empty rest) :=
      ratingAfterPrefix choose criterion agree (width report) Bits.empty report
    _ = rating choose (width report) report := Eq.trans (Option.mapCong _ _ _ (rest => Bits.emptyAppend rest)) (Option.mapId _)

--| Part 2 is the puzzle's answer, for every list of numbers: the same
--| number, or no number on both sides.
theorem part2Correct (report: List Bits): solvePart2 report = lifeSupportRating report :=
  rewrite ratingCorrect mostCommon mostCommonAt mostCommonAfterPrefix report,
    ratingCorrect (column => not (mostCommon column)) leastCommonAt leastCommonAfterPrefix report in cases
