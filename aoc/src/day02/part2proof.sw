-- Why part 2 is right: `part2Correct` says the printed part 2 is `part2Spec`,
-- the puzzle's own method (walk every id of every range, keep those whose
-- digits are some block written two or more times, add them up), for every
-- input.
--
-- The outline, for one id x with L digits (a Lean 4 prototype of the same
-- proof is in comparisons/aoc-day02-general/):
-- - A rotation of the digits by p places that leaves them unchanged is a
--   *period* (`Period`). Periods add and subtract, so the remainder of a
--   period divided by the smallest positive period p0 is again a period, and
--   smaller than p0: it is 0. So every period is a multiple of p0
--   (`periodDvd`). The smallest period is found by a search
--   (`smallestPeriod`), and K = L / p0 is how many times the smallest block
--   is written (`blockCount`).
-- - x's digits are a block written n times exactly when L / n is a period
--   (`writtenPeriod`, `periodWritten`), that is when n divides K
--   (`copiesDivides`); and x repeats exactly when K >= 2 (`repeatsBlocks`).
-- - The program weighs repeat count n by `plus n - minus n`, defined so that
--   over the divisors of K from 2 on, plus adds up to one more than minus
--   when K >= 2 (`plusOneMore`). So x's plus terms are its minus terms, plus
--   x itself exactly when x repeats (`idPlusMinus`).
-- - `repeated r k n` adds the ids of the range whose digits are a k-digit
--   block written n times (`repeatedIds`), and swapping the sums over ids,
--   block lengths and repeat counts finishes it (`weightedIds`, `rangeSplit`).
--   Everything stays in natural numbers.

namespace Aoc.Day02.Proofs
import Aoc.Common (Range, rangeEnd)
import Aoc.Day02 (..)
import Std (Eq)

-- (1) n copies ------------------------------------------------------------
-- The twice* lemmas of day02.sw, for any number of copies n >= 2.

-- The digits `p` written n times make `fromDigits p` written n times.
theorem fromDigitsRep (p: List Nat): (n: Nat) -> Nat.fromDigits (List.concat (List.replicate n p)) = writeTimes (List.length p) (Nat.fromDigits p) n
  | Zero   => rfl
  | Succ n =>
    calc Nat.fromDigits (List.concat (List.replicate (Succ n) p))
      _ = Nat.fromDigits (List.append (List.concat (List.replicate n p)) p) := Eq.cong Nat.fromDigits (List.concatReplicateSnoc p n)
      _ = Nat.fromDigits (List.concat (List.replicate n p)) * Nat.pow 10 (List.length p) + Nat.fromDigits p := Nat.fromDigitsAppend (List.concat (List.replicate n p)) p
      _ = writeTimes (List.length p) (Nat.fromDigits p) n * Nat.pow 10 (List.length p) + Nat.fromDigits p := rewrite fromDigitsRep p n

theorem repAppend (x: Nat) (k: Nat) (n: Nat) (hq: writtenAs (Nat.digits x) k n = True):
    List.concat (List.replicate n (List.take k (Nat.digits x))) = Nat.digits x :=
  Decidable.toBoolSound (List.decEq (\a b => Nat.decEq a b) (List.concat (List.replicate n (List.take k (Nat.digits x)))) (Nat.digits x)) hq

-- With two or more copies the block is k digits long (it can't be all of x).
theorem repBlockLength (x: Nat) (k: Nat) (m: Nat) (hq: writtenAs (Nat.digits x) k (Succ (Succ m)) = True): List.length (List.take k (Nat.digits x)) = k :=
  match e: Nat.leq k (List.length (Nat.digits x)) with
    | True  => List.lengthTake k (Nat.digits x) e
    | False => Void.exfalso (Nat.lessIrrefl (List.length (Nat.digits x))
      (calc Succ (List.length (Nat.digits x))
        _ <= List.length (Nat.digits x) + List.length (Nat.digits x) := Nat.leCongLeft (List.length (Nat.digits x) + 1) (Succ (List.length (Nat.digits x))) (List.length (Nat.digits x) + List.length (Nat.digits x)) (Nat.addOne (List.length (Nat.digits x))) (Nat.leAddCong (List.length (Nat.digits x)) 1 (List.length (Nat.digits x)) (Nat.digitsNonEmpty x))
        _ <= List.length (Nat.digits x) + (List.length (Nat.digits x) + List.length (List.concat (List.replicate m (Nat.digits x)))) := Nat.leAddCong (List.length (Nat.digits x)) (List.length (Nat.digits x)) (List.length (Nat.digits x) + List.length (List.concat (List.replicate m (Nat.digits x)))) (Nat.leAddRight (List.length (Nat.digits x)) (List.length (List.concat (List.replicate m (Nat.digits x)))))
        _ = List.length (List.concat (List.replicate (Succ (Succ m)) (Nat.digits x))) := Eq.sym (Eq.trans (List.lengthAppend (Nat.digits x) (List.append (Nat.digits x) (List.concat (List.replicate m (Nat.digits x))))) (Eq.cong (\t => List.length (Nat.digits x) + t) (List.lengthAppend (Nat.digits x) (List.concat (List.replicate m (Nat.digits x))))))
        _ = List.length (List.concat (List.replicate (Succ (Succ m)) (List.take k (Nat.digits x)))) := Eq.cong (\l => List.length (List.concat (List.replicate (Succ (Succ m)) l))) (Eq.sym (List.takeAll k (Nat.digits x) (Nat.lessLe (List.length (Nat.digits x)) k (Nat.leqFalse k (List.length (Nat.digits x)) e))))
        _ = List.length (Nat.digits x) := Eq.cong List.length (repAppend x k (Succ (Succ m)) hq)))

-- n copies of a k-digit block: n * k digits.
theorem repCount (x: Nat) (k: Nat) (m: Nat) (hq: writtenAs (Nat.digits x) k (Succ (Succ m)) = True): Succ (Succ m) * k = List.length (Nat.digits x) :=
  calc Succ (Succ m) * k
    _ = Succ (Succ m) * List.length (List.take k (Nat.digits x)) := rewrite repBlockLength x k m hq
    _ = List.length (List.concat (List.replicate (Succ (Succ m)) (List.take k (Nat.digits x))))
        := Eq.sym (List.lengthConcatReplicate (List.take k (Nat.digits x)) (Succ (Succ m)))
    _ = List.length (Nat.digits x) := rewrite repAppend x k (Succ (Succ m)) hq

-- x is its first k digits written n times.
theorem repValue (x: Nat) (k: Nat) (m: Nat) (hq: writtenAs (Nat.digits x) k (Succ (Succ m)) = True):
    writeTimes k (Nat.fromDigits (List.take k (Nat.digits x))) (Succ (Succ m)) = x :=
  calc writeTimes k (Nat.fromDigits (List.take k (Nat.digits x))) (Succ (Succ m))
    _ = writeTimes (List.length (List.take k (Nat.digits x))) (Nat.fromDigits (List.take k (Nat.digits x))) (Succ (Succ m)) := Eq.cong (\t => writeTimes t (Nat.fromDigits (List.take k (Nat.digits x))) (Succ (Succ m))) (Eq.sym (repBlockLength x k m hq))
    _ = Nat.fromDigits (List.concat (List.replicate (Succ (Succ m)) (List.take k (Nat.digits x)))) := Eq.sym (fromDigitsRep (List.take k (Nat.digits x)) (Succ (Succ m)))
    _ = Nat.fromDigits (Nat.digits x) := Eq.cong Nat.fromDigits (repAppend x k (Succ (Succ m)) hq)
    _ = x := Nat.fromDigitsDigits x

-- Two or more copies of at least one digit: x isn't 0.
theorem posOfCount: (x: Nat) -> (k: Nat) -> (m: Nat) -> 1 <= k -> Succ (Succ m) * k = List.length (Nat.digits x) -> 1 <= x
  | Zero,   Zero,   m, hk, e => Void.exfalso (Bool.falseNotTrue hk)
  | Zero,   Succ j, m, hk, e =>
    Void.exfalso (Nat.succNotZero (j + (j + m * Succ j))
      (Eq.trans (Eq.sym (Nat.addSucc j (j + m * Succ j))) (Nat.succInjective (j + (Succ j + m * Succ j)) 0 e)))
  | Succ x, k,      m, hk, e => rfl

theorem repBelow (x: Nat) (k: Nat) (m: Nat) (hq: writtenAs (Nat.digits x) k (Succ (Succ m)) = True):
    Nat.fromDigits (List.take k (Nat.digits x)) < Nat.pow 10 k :=
  calc Nat.fromDigits (List.take k (Nat.digits x))
    _ < Nat.pow 10 (List.length (List.take k (Nat.digits x)))
        := Nat.fromDigitsBound (List.take k (Nat.digits x)) (Nat.digitsTake k (Nat.digits x) (Nat.digitsDigits x))
    _ = Nat.pow 10 k := rewrite repBlockLength x k m hq

theorem repAbove (x: Nat) (k: Nat) (m: Nat) (hk: 1 <= k) (hq: writtenAs (Nat.digits x) k (Succ (Succ m)) = True):
    Nat.pow 10 (k - 1) <= Nat.fromDigits (List.take k (Nat.digits x)) :=
  J (\t q => Nat.pow 10 (t - 1) <= Nat.fromDigits (List.take k (Nat.digits x)))
    (Nat.fromDigitsHeadBound (List.take k (Nat.digits x))
      (Nat.leCongRight 1 (List.headOr 0 (Nat.digits x)) (List.headOr 0 (List.take k (Nat.digits x)))
        (Eq.sym (List.headTake 0 k (Nat.digits x) hk))
        (Nat.digitsHead x (posOfCount x k m hk (repCount x k m hq)))))
    (repBlockLength x k m hq)

-- The other way: a block of k digits (no leading 0) written n >= 1 times
-- has those digits n times.
theorem writeTimesPos (k: Nat) (b: Nat) (hb: 1 <= b) (n: Nat): 1 <= writeTimes k b (Succ n) :=
  Nat.leTrans 1 b (writeTimes k b n * Nat.pow 10 k + b) hb (Nat.leAddLeft (writeTimes k b n * Nat.pow 10 k) b)

theorem digitsRep (b: Nat) (hb: 1 <= b): (n: Nat) ->
    Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n)) = List.concat (List.replicate (Succ n) (Nat.digits b))
  | Zero   => Eq.sym (List.appendNil (Nat.digits b))
  | Succ n =>
    calc Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n) * Nat.pow 10 (List.length (Nat.digits b)) + b)
      _ = Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n) * Nat.pow 10 (List.length (Nat.digits b)) + Nat.fromDigits (Nat.digits b)) := rewrite Nat.fromDigitsDigits b
      _ = List.append (Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n))) (Nat.digits b) := Nat.digitsShift (Nat.digits b) (writeTimes (List.length (Nat.digits b)) b (Succ n)) (writeTimesPos (List.length (Nat.digits b)) b hb n) (Nat.digitsDigits b)
      _ = List.append (List.concat (List.replicate (Succ n) (Nat.digits b))) (Nat.digits b) := rewrite digitsRep b hb n
      _ = List.concat (List.replicate (Succ (Succ n)) (Nat.digits b)) := Eq.sym (List.concatReplicateSnoc (Nat.digits b) (Succ n))

theorem writtenRepOf (p: List Nat) (k: Nat) (hk: List.length p = k) (n: Nat): writtenAs (List.concat (List.replicate (Succ n) p)) k (Succ n) = True :=
  Decidable.toBoolOf (List.decEq (\a b => Nat.decEq a b) (List.concat (List.replicate (Succ n) (List.take k (List.concat (List.replicate (Succ n) p))))) (List.concat (List.replicate (Succ n) p)))
    (rewrite <- hk, List.takeAppend p (List.concat (List.replicate n p)))

theorem repDigits (j: Nat) (b: Nat) (h1: Nat.pow 10 j <= b) (h2: b < Nat.pow 10 (Succ j)) (n: Nat):
    writtenAs (Nat.digits (writeTimes (Succ j) b (Succ n))) (Succ j) (Succ n) = True :=
  rewrite <- (calc List.concat (List.replicate (Succ n) (Nat.digits b))
      _ = Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n))
          := Eq.sym (digitsRep b (Nat.leTrans 1 (Nat.pow 10 j) b (Nat.powSuccPos 9 j) h1) n)
      _ = Nat.digits (writeTimes (Succ j) b (Succ n)) := rewrite Nat.digitsLength j b h1 h2)
    in writtenRepOf (Nat.digits b) (Succ j) (Nat.digitsLength j b h1 h2) n

theorem repInjective (k: Nat) (b: Nat) (v: Nat) (m: Nat) (e: writeTimes k b (Succ m) = writeTimes k v (Succ m)): b = v :=
  Nat.mulSuccCancel b v (Nat.pow 10 k * multiplier k m)
    (calc b * Succ (Nat.pow 10 k * multiplier k m)
      _ = b * multiplier k (Succ m)   := rewrite multiplierSucc k m
      _ = writeTimes k b (Succ m)     := Eq.sym (writeTimesMul k b (Succ m))
      _ = writeTimes k v (Succ m)     := e
      _ = v * multiplier k (Succ m)   := writeTimesMul k v (Succ m)
      _ = v * Succ (Nat.pow 10 k * multiplier k m) := rewrite multiplierSucc k m)

-- For one id `x`, block length k and n copies: the blocks written n times
-- that make `x` add up to `x` when x's digits are a k-digit block written n
-- times, and to 0 otherwise (`blockCount` for any n).
theorem blockCountRep (x: Nat) (m: Nat): (k: Nat) -> 1 <= k ->
    List.sumBy (\b => Nat.keepIf x (writeTimes k b (Succ (Succ m)) == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
      = Nat.keepIf x (writtenAs (Nat.digits x) k (Succ (Succ m)))
  | Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ j, h =>
    match hq: writtenAs (Nat.digits x) (Succ j) (Succ (Succ m)) with
      | True =>
        List.sumRangeOne (\b => writeTimes (Succ j) b (Succ (Succ m)) == x) (\b => x) (Nat.fromDigits (List.take (Succ j) (Nat.digits x)))
          (Decidable.toBoolOf (Nat.decEq (writeTimes (Succ j) (Nat.fromDigits (List.take (Succ j) (Nat.digits x))) (Succ (Succ m))) x) (repValue x (Succ j) m hq))
          (\b hb => repInjective (Succ j) b (Nat.fromDigits (List.take (Succ j) (Nat.digits x))) (Succ m)
            (Eq.trans (Decidable.toBoolSound (Nat.decEq (writeTimes (Succ j) b (Succ (Succ m))) x) hb) (Eq.sym (repValue x (Succ j) m hq))))
          (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
          (repAbove x (Succ j) m rfl hq)
          (calc Nat.fromDigits (List.take (Succ j) (Nat.digits x))
            _ < Nat.pow 10 (Succ j)                                  := repBelow x (Succ j) m hq
            _ = Nat.pow 10 j + (Nat.pow 10 (Succ j) - Nat.pow 10 j) := Eq.sym (Nat.addSubCancel (Nat.pow 10 j) (Nat.pow 10 (Succ j)) (Nat.powTenPredLe (Succ j))))
      | False =>
        List.sumRangeNone (\b => writeTimes (Succ j) b (Succ (Succ m)) == x) (\b => x) (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
          (\b h1 h2 => Decidable.toBoolOfNot (Nat.decEq (writeTimes (Succ j) b (Succ (Succ m))) x)
            (\e => Bool.trueNotFalse (Eq.trans
              (Eq.sym (J (\y q => writtenAs (Nat.digits y) (Succ j) (Succ (Succ m)) = True)
                (repDigits j b h1
                  (calc b
                    _ < Nat.pow 10 j + (Nat.pow 10 (Succ j) - Nat.pow 10 j) := h2
                    _ = Nat.pow 10 (Succ j) := Nat.addSubCancel (Nat.pow 10 j) (Nat.pow 10 (Succ j)) (Nat.powTenPredLe (Succ j)))
                  (Succ m))
                e))
              hq)))

-- One block length, as a sum over the ids of the range (`blocksAsIds` for any n).
theorem blocksAsIdsRep (r: Range) (k: Nat) (n: Nat):
    repeatedSpec r k n
      = List.sumBy (\x => List.sumBy (\b => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
          (List.rangeFrom (r.to + 1 - r.from) r.from) :=
  calc repeatedSpec r k n
    -- filtering the block ids by the range is summing "the id if it is in the range"
    _ = List.sumBy (\y => Nat.keepIf y (r.from <= y && y <= r.to)) (List.map (\b => writeTimes k b n) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
        := List.sumFilter (\x => r.from <= x && x <= r.to) (List.map (\b => writeTimes k b n) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
    _ = List.sumBy (\b => Nat.keepIf (writeTimes k b n) (r.from <= writeTimes k b n && writeTimes k b n <= r.to)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
        := List.sumByMap (\y => Nat.keepIf y (r.from <= y && y <= r.to)) (\b => writeTimes k b n) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
    -- and, for each block, "the id if it is in the range" is the sum over the range ids that equal it
    _ = List.sumBy (\b => List.sumBy (\x => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (r.to + 1 - r.from) r.from)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
        := List.sumByCongr (\b => Nat.keepIf (writeTimes k b n) (r.from <= writeTimes k b n && writeTimes k b n <= r.to))
             (\b => List.sumBy (\x => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (r.to + 1 - r.from) r.from))
             (\b => Eq.sym (sumIdsEq r.from r.to (writeTimes k b n)))
             (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
    _ = List.sumBy (\x => List.sumBy (\b => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))) (List.rangeFrom (r.to + 1 - r.from) r.from)
        := List.sumBySwap (\b x => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (r.to + 1 - r.from) r.from) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))

-- (1) `repeated r k n` adds the ids of the range whose digits are a k-digit
-- block written n times.
theorem repeatedIds (r: Range) (k: Nat) (hk: 1 <= k): (n: Nat) -> 2 <= n ->
    repeated r k n = List.sumBy (\x => Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids
  | Zero,          h => Void.exfalso (Bool.falseNotTrue h)
  | Succ Zero,     h => Void.exfalso (Bool.falseNotTrue h)
  | Succ (Succ m), h =>
    calc repeated r k (Succ (Succ m))
      _ = repeatedSpec r k (Succ (Succ m)) := repeatedCorrect r k (Succ (Succ m))
      _ = List.sumBy (\x => List.sumBy (\b => Nat.keepIf x (writeTimes k b (Succ (Succ m)) == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))) r.ids
          := blocksAsIdsRep r k (Succ (Succ m))
      _ = List.sumBy (\x => Nat.keepIf x (writtenAs (Nat.digits x) k (Succ (Succ m)))) r.ids
          := List.sumByCongr (\x => List.sumBy (\b => Nat.keepIf x (writeTimes k b (Succ (Succ m)) == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
               (\x => Nat.keepIf x (writtenAs (Nat.digits x) k (Succ (Succ m)))) (\x => blockCountRep x m k hk) r.ids

-- The same facts for any n >= 2.
theorem countOf (x: Nat) (k: Nat): (n: Nat) -> 2 <= n -> writtenAs (Nat.digits x) k n = True -> n * k = List.length (Nat.digits x)
  | Zero,          h, hq => Void.exfalso (Bool.falseNotTrue h)
  | Succ Zero,     h, hq => Void.exfalso (Bool.falseNotTrue h)
  | Succ (Succ m), h, hq => repCount x k m hq

theorem valueOf (x: Nat) (k: Nat): (n: Nat) -> 2 <= n -> writtenAs (Nat.digits x) k n = True -> writeTimes k (Nat.fromDigits (List.take k (Nat.digits x))) n = x
  | Zero,          h, hq => Void.exfalso (Bool.falseNotTrue h)
  | Succ Zero,     h, hq => Void.exfalso (Bool.falseNotTrue h)
  | Succ (Succ m), h, hq => repValue x k m hq

theorem aboveOf (x: Nat) (k: Nat) (hk: 1 <= k): (n: Nat) -> 2 <= n -> writtenAs (Nat.digits x) k n = True -> Nat.pow 10 (k - 1) <= Nat.fromDigits (List.take k (Nat.digits x))
  | Zero,          h, hq => Void.exfalso (Bool.falseNotTrue h)
  | Succ Zero,     h, hq => Void.exfalso (Bool.falseNotTrue h)
  | Succ (Succ m), h, hq => repAbove x k m hk hq

theorem belowOf (x: Nat) (k: Nat): (n: Nat) -> 2 <= n -> writtenAs (Nat.digits x) k n = True -> Nat.fromDigits (List.take k (Nat.digits x)) < Nat.pow 10 k
  | Zero,          h, hq => Void.exfalso (Bool.falseNotTrue h)
  | Succ Zero,     h, hq => Void.exfalso (Bool.falseNotTrue h)
  | Succ (Succ m), h, hq => repBelow x k m hq

theorem blockAtMost (x: Nat) (k: Nat) (n: Nat) (hn: 2 <= n) (hq: writtenAs (Nat.digits x) k n = True): k <= List.length (Nat.digits x) :=
  Nat.leCongRight k (k * n) (List.length (Nat.digits x)) (Eq.trans (Nat.mulComm k n) (countOf x k n hn hq)) (Nat.leMulPos k n (Nat.leTrans 1 2 n rfl hn))


-- The digits of x are some block written n times.
def copies (x: Nat) (n: Nat): Bool :=
  List.rangeFrom (Nat.digits x).length 1 |> .any (\k => writtenAs (Nat.digits x) k n)

-- For one id and repeat count, over all block lengths up to `size`: x if
-- some block written n times makes x, else 0.
theorem collapse (x: Nat) (n: Nat) (hn: 2 <= n) (size: Nat) (hLS: List.length (Nat.digits x) <= size):
    List.sumBy (\k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1) = Nat.keepIf x (copies x n) :=
  match hc: copies x n with
    | True =>
      List.anyRangeElim (\k => writtenAs (Nat.digits x) k n) (List.sumBy (\k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1) = x) (List.length (Nat.digits x)) 1 hc
        (\k0 h1 h2 hk0 => List.sumRangeOne (\k => writtenAs (Nat.digits x) k n) (\k => x) k0 hk0
          (\k hk => Nat.mulCancelLeft n (Nat.leTrans 1 2 n rfl hn) k k0 (Eq.trans (countOf x k n hn hk) (Eq.sym (countOf x k0 n hn hk0))))
          size 1 h1 (Nat.leTrans (Succ k0) (Succ (List.length (Nat.digits x))) (Succ size) h2 hLS))
    | False =>
      List.sumRangeNone (\k => writtenAs (Nat.digits x) k n) (\k => x) size 1
        (\k h1 h2 =>
          match t: writtenAs (Nat.digits x) k n with
            | True  => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (List.anyRangeIntro (\k => writtenAs (Nat.digits x) k n) (List.length (Nat.digits x)) 1 k h1 (blockAtMost x k n hn t) t)) hc))
            | False => rfl)

-- The ids of a range have at most as many digits as its end.
theorem idsBelow (r: Range) (x: Nat) (h1: r.from <= x) (h2: x < r.from + r.size): List.length (Nat.digits x) <= List.length (Nat.digits r.to) :=
  Nat.digitsLengthLe x (List.length (Nat.digits r.to)) (Nat.digitsNonEmpty r.to)
    (Nat.leTrans (Succ x) (Succ r.to) (Nat.pow 10 (List.length (Nat.digits r.to))) (rangeEnd r.from r.to x h1 h2) (Nat.ltPowTenDigits r.to))


-- (2) The weights ------------------------------------------------------------
-- Over the divisors of m from 2 on, `plus` adds up to one more than `minus`
-- when m >= 2, and to the same when m = 1 (`plusOneMore`).

-- More fuel doesn't change `weightFuel`.
theorem weightFuelEnough: (f: Nat) -> (g: Nat) -> (s: Bool) -> (n: Nat) -> n < f -> n < g -> weightFuel f s n = weightFuel g s n
  | Zero,   g,      s,     n, hf, hg => Void.exfalso (Bool.falseNotTrue hf)
  | Succ f, Zero,   s,     n, hf, hg => Void.exfalso (Bool.falseNotTrue hg)
  | Succ f, Succ g, True,  n, hf, hg =>
    Eq.cong (\t => 1 + t)
      (List.sumRangeCongr (\d => if Nat.divides d n then weightFuel f False d else 0) (\d => if Nat.divides d n then weightFuel g False d else 0) (n - 2) 2
        (\d d1 d2 => Eq.cong (\t => if Nat.divides d n then t else 0)
          (weightFuelEnough f g False d (Nat.leTrans (Succ d) n f (Nat.ltOfRunSub 2 d n d1 d2) hf) (Nat.leTrans (Succ d) n g (Nat.ltOfRunSub 2 d n d1 d2) hg))))
  | Succ f, Succ g, False, n, hf, hg =>
    List.sumRangeCongr (\d => if Nat.divides d n then weightFuel f True d else 0) (\d => if Nat.divides d n then weightFuel g True d else 0) (n - 2) 2
      (\d d1 d2 => Eq.cong (\t => if Nat.divides d n then t else 0)
        (weightFuelEnough f g True d (Nat.leTrans (Succ d) n f (Nat.ltOfRunSub 2 d n d1 d2) hf) (Nat.leTrans (Succ d) n g (Nat.ltOfRunSub 2 d n d1 d2) hg)))

-- The divisors below m = j + 2 with the fuel m (as in `plus m`), and with
-- their own fuel (as in `plus d`).
theorem belowFuel (s: Bool) (j: Nat):
    divisorWeights (\d => weightFuel (Succ (Succ j)) s d) (Succ (Succ j)) j = divisorWeights (\d => weightFuel (Succ d) s d) (Succ (Succ j)) j :=
  List.sumRangeCongr (\d => if Nat.divides d (Succ (Succ j)) then weightFuel (Succ (Succ j)) s d else 0)
    (\d => if Nat.divides d (Succ (Succ j)) then weightFuel (Succ d) s d else 0) j 2
    (\d d1 d2 => Eq.cong (\t => if Nat.divides d (Succ (Succ j)) then t else 0) (weightFuelEnough (Succ (Succ j)) (Succ d) s d d2 (Nat.leRefl (Succ d))))

-- m itself is the last divisor.
theorem divisorWeightsTop (w: Nat -> Nat) (j: Nat): divisorWeights w (Succ (Succ j)) (Succ j) = divisorWeights w (Succ (Succ j)) j + w (Succ (Succ j)) :=
  let f: Nat -> Nat := \d => if Nat.divides d (Succ (Succ j)) then w d else 0
  calc List.sumBy f (List.rangeFrom (Succ j) 2)
    _ = List.sumBy f (List.rangeFrom (j + 1) 2) := Eq.cong (\t => List.sumBy f (List.rangeFrom t 2)) (Eq.sym (Nat.addOne j))
    _ = List.sumBy f (List.append (List.rangeFrom j 2) (List.rangeFrom 1 (2 + j))) := Eq.cong (List.sumBy f) (List.rangeFromAppend j 1 2)
    _ = List.sumBy f (List.rangeFrom j 2) + List.sumBy f (List.rangeFrom 1 (2 + j)) := List.sumByAppend f (List.rangeFrom j 2) (List.rangeFrom 1 (2 + j))
    _ = List.sumBy f (List.rangeFrom j 2) + w (Succ (Succ j))
        := Eq.cong (\c => List.sumBy f (List.rangeFrom j 2) + (if c then w (Succ (Succ j)) else 0)) (Nat.dividesSelf (Succ (Succ j)))

theorem plusOneMore: (m: Nat) -> 1 <= m -> divisorWeights plus m (m - 1) = Bool.toNat (Nat.leq 2 m) + divisorWeights minus m (m - 1)
  | Zero,          h => Void.exfalso (Bool.falseNotTrue h)
  | Succ Zero,     h => rfl
  | Succ (Succ j), h =>
    calc divisorWeights plus (Succ (Succ j)) (Succ j)
      _ = divisorWeights plus (Succ (Succ j)) j + plus (Succ (Succ j)) := divisorWeightsTop plus j
      -- `plus m` is 1 more than the minus weights of the divisors below m
      _ = divisorWeights plus (Succ (Succ j)) j + (1 + divisorWeights minus (Succ (Succ j)) j)
          := Eq.cong (\t => divisorWeights plus (Succ (Succ j)) j + (1 + t)) (belowFuel False j)
      _ = 1 + (divisorWeights minus (Succ (Succ j)) j + divisorWeights plus (Succ (Succ j)) j)
          := Eq.trans (Nat.addLeftComm (divisorWeights plus (Succ (Succ j)) j) 1 (divisorWeights minus (Succ (Succ j)) j))
               (Eq.cong (\t => 1 + t) (Nat.addComm (divisorWeights plus (Succ (Succ j)) j) (divisorWeights minus (Succ (Succ j)) j)))
      -- and `minus m` is the plus weights of the same divisors
      _ = 1 + (divisorWeights minus (Succ (Succ j)) j + minus (Succ (Succ j)))
          := Eq.cong (\t => 1 + (divisorWeights minus (Succ (Succ j)) j + t)) (Eq.sym (belowFuel True j))
      _ = 1 + divisorWeights minus (Succ (Succ j)) (Succ j) := Eq.cong (\t => 1 + t) (Eq.sym (divisorWeightsTop minus j))

-- Divisors of m beyond m count for nothing.
theorem divisorWeightsAll (w: Nat -> Nat): (m: Nat) -> 1 <= m -> (c: Nat) -> m <= Succ c -> divisorWeights w m c = divisorWeights w m (m - 1)
  | Zero,   hm, c, hc => Void.exfalso (Bool.falseNotTrue hm)
  | Succ k, hm, c, hc =>
    let f: Nat -> Nat := \d => if Nat.divides d (Succ k) then w d else 0
    calc List.sumBy f (List.rangeFrom c 2)
      _ = List.sumBy f (List.rangeFrom (k + (c - k)) 2) := Eq.cong (\t => List.sumBy f (List.rangeFrom t 2)) (Eq.sym (Nat.addSubCancel k c hc))
      _ = List.sumBy f (List.append (List.rangeFrom k 2) (List.rangeFrom (c - k) (2 + k))) := Eq.cong (List.sumBy f) (List.rangeFromAppend k (c - k) 2)
      _ = List.sumBy f (List.rangeFrom k 2) + List.sumBy f (List.rangeFrom (c - k) (2 + k)) := List.sumByAppend f (List.rangeFrom k 2) (List.rangeFrom (c - k) (2 + k))
      _ = List.sumBy f (List.rangeFrom k 2) + 0
          := Eq.cong (\t => List.sumBy f (List.rangeFrom k 2) + t)
               (Eq.trans (List.sumByCongr f (\d => Nat.keepIf (w d) (Nat.divides d (Succ k))) (\d => Nat.ifKeep (w d) (Nat.divides d (Succ k))) (List.rangeFrom (c - k) (2 + k)))
                 (List.sumRangeNone (\d => Nat.divides d (Succ k)) w (c - k) (2 + k) (\d d1 d2 => Nat.dividesSmall d (Succ k) rfl d1)))
      _ = List.sumBy f (List.rangeFrom k 2) := Nat.addZero (List.sumBy f (List.rangeFrom k 2))

theorem mulKeep (v: Nat) (x: Nat): (b: Bool) -> v * Nat.keepIf x b = x * (if b then v else 0)
  | True  => Nat.mulComm v x
  | False => Eq.trans (Nat.mulZero v) (Eq.sym (Nat.mulZero x))


-- (3) Periods ----------------------------------------------------------------

-- Rotating the first `len` values of g by p places leaves them unchanged.
def Period (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat): Prop := (i: Nat) -> i < len -> g ((i + p) % len) = g i

theorem periodZero (g: Nat -> Nat) (len: Nat) (hl: len != 0): Period g len hl 0 :=
  \i hi => Eq.cong g (Eq.trans (Eq.cong (\y => y % len) (Nat.addZero i)) (Nat.modSmall i len hi))

theorem periodLen (g: Nat -> Nat) (len: Nat) (hl: len != 0): Period g len hl len :=
  \i hi => Eq.cong g (Eq.trans (Eq.cong (\y => y % len) (Nat.addComm i len)) (Eq.trans (Nat.addModSelf len i) (Nat.modSmall i len hi)))

-- Doing one rotation and then the other is a rotation too.
theorem periodAdd (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat) (q: Nat) (hp: Period g len hl p) (hq: Period g len hl q): Period g len hl (p + q) :=
  \i hi =>
    calc g ((i + (p + q)) % len)
      _ = g (((i + p) + q) % len)       := Eq.cong (\y => g (y % len)) (Eq.sym (Nat.addAssoc i p q))
      _ = g (((i + p) % len + q) % len) := Eq.cong g (Eq.sym (Nat.modAddMod (i + p) q len))
      _ = g ((i + p) % len)             := hq ((i + p) % len) (Nat.modLess (i + p) len hl)
      _ = g i                           := hp i hi

theorem periodSub (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat) (q: Nat) (hp: Period g len hl p) (hq: Period g len hl q) (hle: q <= p): Period g len hl (p - q) :=
  \i hi =>
    calc g ((i + (p - q)) % len)
      _ = g (((i + (p - q)) % len + q) % len) := Eq.sym (hq ((i + (p - q)) % len) (Nat.modLess (i + (p - q)) len hl))
      _ = g ((i + (p - q) + q) % len)         := Eq.cong g (Nat.modAddMod (i + (p - q)) q len)
      _ = g ((i + p) % len)
          := Eq.cong (\y => g (y % len)) (Eq.trans (Nat.addAssoc i (p - q) q) (Eq.cong (\t => i + t) (Eq.trans (Nat.addComm (p - q) q) (Nat.addSubCancel q p hle))))
      _ = g i                                 := hp i hi

theorem periodMul (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat) (hp: Period g len hl p): (t: Nat) -> Period g len hl (t * p)
  | Zero,   i, hi => periodZero g len hl i hi
  | Succ t, i, hi => periodAdd g len hl p (t * p) hp (\j hj => periodMul g len hl p hp t j hj) i hi

-- The same as a test, which a search can run.
def isPeriod (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat): Bool := List.range len |> .all (\i => g ((i + p) % len) == g i)

theorem periodOfTest (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat) (h: isPeriod g len hl p = True): Period g len hl p :=
  \i hi => Decidable.toBoolSound (Nat.decEq (g ((i + p) % len)) (g i)) (List.allRangeElim (\i => g ((i + p) % len) == g i) len 0 h i (Nat.zeroLe i) hi)

theorem periodTest (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat) (h: Period g len hl p): isPeriod g len hl p = True :=
  List.allRangeIntro (\i => g ((i + p) % len) == g i) len 0 (\i h1 h2 => Decidable.toBoolOf (Nat.decEq (g ((i + p) % len)) (g i)) (h i h2))

-- A period below the smallest positive one, `Succ j`, is 0.
theorem periodBelow (g: Nat -> Nat) (len: Nat) (hl: len != 0) (j: Nat) (hmin: (r: Nat) -> r < j -> isPeriod g len hl (Succ r) = False):
    (r: Nat) -> Period g len hl r -> r < Succ j -> r = 0
  | Zero,   hr, lt => rfl
  | Succ r, hr, lt => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (periodTest g len hl (Succ r) hr)) (hmin r lt)))

-- The heart: every period is a multiple of the smallest positive one (the
-- remainder of the division is a smaller period).
theorem periodDvd (g: Nat -> Nat) (len: Nat) (hl: len != 0) (j: Nat) (hp0: Period g len hl (Succ j))
    (hmin: (r: Nat) -> r < j -> isPeriod g len hl (Succ r) = False) (p: Nat) (hp: Period g len hl p): p % Succ j = 0 :=
  let t := p / Succ j
  let rest: Period g len hl (p - t * Succ j) :=
    periodSub g len hl p (t * Succ j) hp (periodMul g len hl (Succ j) hp0 t) (Nat.divMulLe p (Succ j) (Nat.succNotZero j))
  let e: p - t * Succ j = p % Succ j :=
    Eq.trans (Eq.cong (\y => y - t * Succ j) (Eq.trans (Nat.divMod p (Succ j) (Nat.succNotZero j)) (Nat.addComm (t * Succ j) (p % Succ j))))
      (Nat.addSub (p % Succ j) (t * Succ j))
  periodBelow g len hl j hmin (p % Succ j) (J (\y q => Period g len hl y) rest e) (Nat.modLess p (Succ j) (Nat.succNotZero j))


-- (4) Blocks are periods -----------------------------------------------------

-- The digit at position i (0 past the end).
def digitAt (ds: List Nat) (i: Nat): Nat := List.getOr 0 i ds

-- Digits that are their first k digits written n times: each digit is the
-- one at its position within the first k.
theorem writtenBlock (ds: List Nat) (k: Nat) (n: Nat) [auto hk: k != 0] (hn: 1 <= n) (e: k * n = List.length ds) (hw: writtenAs ds k n = True)
    (j: Nat) (hj: j < List.length ds): digitAt ds j = digitAt ds (j % k) :=
  calc List.getOr 0 j ds
    _ = List.getOr 0 j (List.concat (List.replicate n (List.take k ds)))
        := Eq.cong (\l => List.getOr 0 j l) (Eq.sym (Decidable.toBoolSound (List.decEq (\a b => Nat.decEq a b) (List.concat (List.replicate n (List.take k ds))) ds) hw))
    _ = List.getOr 0 (j % k) (List.take k ds)
        := List.getOrConcatReplicate 0 (List.take k ds) k (List.lengthTake k ds (Nat.leCongRight k (k * n) (List.length ds) e (Nat.leMulPos k n hn))) n j
             (Nat.ltCongRight j (List.length ds) (n * k) (Eq.trans (Eq.sym e) (Nat.mulComm k n)) hj)
    _ = List.getOr 0 (j % k) ds := List.getOrTake 0 k (j % k) ds (Nat.modLess j k hk)

theorem writtenPeriod (ds: List Nat) (hl: List.length ds != 0) (k: Nat) (n: Nat) [auto hk: k != 0] (hn: 1 <= n) (e: k * n = List.length ds)
    (hw: writtenAs ds k n = True): Period (digitAt ds) (List.length ds) hl k :=
  \i hi =>
    calc digitAt ds ((i + k) % List.length ds)
      _ = digitAt ds ((i + k) % List.length ds % k) := writtenBlock ds k n hn e hw ((i + k) % List.length ds) (Nat.modLess (i + k) (List.length ds) hl)
      _ = digitAt ds ((i + k) % k)                  := Eq.cong (digitAt ds) (Nat.modModOfMul (i + k) (List.length ds) k n (Eq.trans (Eq.sym e) (Nat.mulComm k n)))
      _ = digitAt ds (i % k)                        := Eq.cong (digitAt ds) (Eq.trans (Eq.cong (\y => y % k) (Nat.addComm i k)) (Nat.addModSelf k i))
      _ = digitAt ds i                              := Eq.sym (writtenBlock ds k n hn e hw i hi)

-- With period k, each digit is the one at its position within the first k.
theorem periodBlock (ds: List Nat) (hl: List.length ds != 0) (k: Nat) [auto hk: k != 0] (hp: Period (digitAt ds) (List.length ds) hl k)
    (i: Nat) (hi: i < List.length ds): digitAt ds i = digitAt ds (i % k) :=
  calc digitAt ds i
    _ = digitAt ds (i % List.length ds)                     := Eq.cong (digitAt ds) (Eq.sym (Nat.modSmall i (List.length ds) hi))
    _ = digitAt ds ((i % k + (i / k) * k) % List.length ds)
        := Eq.cong (\y => digitAt ds (y % List.length ds)) (Eq.trans (Nat.divMod i k hk) (Nat.addComm ((i / k) * k) (i % k)))
    _ = digitAt ds (i % k)
        := periodMul (digitAt ds) (List.length ds) hl k hp (i / k) (i % k) (Nat.leTrans (Succ (i % k)) (Succ i) (List.length ds) (Nat.subLe i ((i / k) * k)) hi)

theorem periodWritten (ds: List Nat) (hl: List.length ds != 0) (k: Nat) (n: Nat) [auto hk: k != 0] (hn: 1 <= n) (e: k * n = List.length ds)
    (hp: Period (digitAt ds) (List.length ds) hl k): writtenAs ds k n = True :=
  let ht: List.length (List.take k ds) = k := List.lengthTake k ds (Nat.leCongRight k (k * n) (List.length ds) e (Nat.leMulPos k n hn))
  let len: List.length (List.concat (List.replicate n (List.take k ds))) = n * k :=
    Eq.trans (List.lengthConcatReplicate (List.take k ds) n) (Eq.cong (\t => n * t) ht)
  Decidable.toBoolOf (List.decEq (\a b => Nat.decEq a b) (List.concat (List.replicate n (List.take k ds))) ds)
    (List.extGetOr 0 (List.concat (List.replicate n (List.take k ds))) ds (Eq.trans len (Eq.trans (Nat.mulComm n k) e))
      (\i hi =>
        calc List.getOr 0 i (List.concat (List.replicate n (List.take k ds)))
          _ = List.getOr 0 (i % k) (List.take k ds) := List.getOrConcatReplicate 0 (List.take k ds) k ht n i (Nat.ltCongRight i (List.length (List.concat (List.replicate n (List.take k ds)))) (n * k) len hi)
          _ = List.getOr 0 (i % k) ds               := List.getOrTake 0 k (i % k) ds (Nat.modLess i k hk)
          _ = List.getOr 0 i ds
              := Eq.sym (periodBlock ds hl k hp i (Nat.ltCongRight i (n * k) (List.length ds) (Eq.trans (Nat.mulComm n k) e) (Nat.ltCongRight i (List.length (List.concat (List.replicate n (List.take k ds)))) (n * k) len hi)))))


-- (5) One id -----------------------------------------------------------------

def digitCount (x: Nat): Nat := List.length (Nat.digits x)

theorem digitCountNonZero (x: Nat): digitCount x != 0 := Nat.nonzeroOfPos (digitCount x) (Nat.digitsNonEmpty x)

-- x's digits have period p.
def periodOf (x: Nat) (p: Nat): Bool := isPeriod (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) p

-- x's smallest positive period is `Succ (periodIndex x)`: the first p in
-- 1, 2, ..., digitCount x that passes (the digit count always does).
def periodIndex (x: Nat): Nat := Nat.firstFrom (\j => periodOf x (Succ j)) (digitCount x) 0

def smallestPeriod (x: Nat): Nat := Succ (periodIndex x)

-- How many times x's smallest block is written.
def blockCount (x: Nat): Nat := digitCount x / smallestPeriod x

test "smallest blocks" := List.map blockCount [7, 1212, 123123123, 1213] == [1, 2, 3, 1]

theorem smallestIsPeriod (x: Nat): Period (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (smallestPeriod x) :=
  let top: Succ (digitCount x - 1) = digitCount x := Nat.addSubCancel 1 (digitCount x) (Nat.digitsNonEmpty x)
  periodOfTest (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (smallestPeriod x)
    (Nat.firstFromFound (\j => periodOf x (Succ j)) (digitCount x) 0 (digitCount x - 1) (Nat.zeroLe (digitCount x - 1))
      (Nat.leCongLeft (digitCount x) (Succ (digitCount x - 1)) (digitCount x) (Eq.sym top) (Nat.leRefl (digitCount x)))
      (J (\y q => periodOf x y = True) (periodTest (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (digitCount x) (periodLen (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x))) (Eq.sym top)))

theorem smallestDivides (x: Nat) (p: Nat) (hp: Period (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) p): p % smallestPeriod x = 0 :=
  periodDvd (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (periodIndex x) (smallestIsPeriod x)
    (\r hr => Nat.firstFromBefore (\j => periodOf x (Succ j)) (digitCount x) 0 r (Nat.zeroLe r) hr) p hp

theorem countTimesPeriod (x: Nat): digitCount x = blockCount x * smallestPeriod x :=
  calc digitCount x
    _ = blockCount x * smallestPeriod x + digitCount x % smallestPeriod x := Nat.divMod (digitCount x) (smallestPeriod x) (Nat.succNotZero (periodIndex x))
    _ = blockCount x * smallestPeriod x + 0
        := Eq.cong (\t => blockCount x * smallestPeriod x + t)
             (smallestDivides x (digitCount x) (periodLen (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x)))
    _ = blockCount x * smallestPeriod x := Nat.addZero (blockCount x * smallestPeriod x)

theorem blockCountPos (x: Nat): 1 <= blockCount x :=
  match e: blockCount x with
    | Zero   => Void.exfalso (Bool.falseNotTrue (J (\y q => 1 <= y) (Nat.digitsNonEmpty x) (Eq.trans (countTimesPeriod x) (Eq.cong (\t => t * smallestPeriod x) e))))
    | Succ k => rfl

theorem blockCountLe (x: Nat): blockCount x <= digitCount x :=
  Nat.leCongRight (blockCount x) (blockCount x * smallestPeriod x) (digitCount x) (Eq.sym (countTimesPeriod x)) (Nat.leMulPos (blockCount x) (smallestPeriod x) rfl)

-- A block of k digits written n times: n divides the block count.
theorem dividesOfWritten (x: Nat) (n: Nat) (hn: 2 <= n) (k: Nat) (hk1: 1 <= k) (hw: writtenAs (Nat.digits x) k n = True): Nat.divides n (blockCount x) = True :=
  let hk: k != 0 := Nat.nonzeroOfPos k hk1
  let per := writtenPeriod (Nat.digits x) (digitCountNonZero x) k n (Nat.leTrans 1 2 n rfl hn) (Eq.trans (Nat.mulComm k n) (countOf x k n hn hw)) hw
  -- k is t times the smallest period
  let t := k / smallestPeriod x
  let ek: k = t * smallestPeriod x :=
    Eq.trans (Nat.divMod k (smallestPeriod x) (Nat.succNotZero (periodIndex x)))
      (Eq.trans (Eq.cong (\r => t * smallestPeriod x + r) (smallestDivides x k per)) (Nat.addZero (t * smallestPeriod x)))
  let eK: blockCount x = n * t :=
    Nat.mulSuccCancel (blockCount x) (n * t) (periodIndex x)
      (calc blockCount x * smallestPeriod x
        _ = digitCount x                   := Eq.sym (countTimesPeriod x)
        _ = n * k                          := Eq.sym (countOf x k n hn hw)
        _ = n * (t * smallestPeriod x)     := Eq.cong (\y => n * y) ek
        _ = n * t * smallestPeriod x       := Eq.sym (Nat.mulAssoc n t (smallestPeriod x)))
  J (\y q => Nat.divides n y = True) (Nat.dividesMul n t) (Eq.sym (Eq.trans eK (Nat.mulComm n t)))

-- And back: if n divides the block count, the digits are a block written n times.
theorem writtenOfDivides (x: Nat) (n: Nat) (hn: 2 <= n): (t: Nat) -> blockCount x = t * n -> copies x n = True
  | Zero,   e => Void.exfalso (Bool.falseNotTrue (J (\y q => 1 <= y) (blockCountPos x) e))
  | Succ t, e =>
    let k := Succ t * smallestPeriod x
    let ekn: k * n = digitCount x :=
      calc (Succ t * smallestPeriod x) * n
        _ = Succ t * (smallestPeriod x * n) := Nat.mulAssoc (Succ t) (smallestPeriod x) n
        _ = Succ t * (n * smallestPeriod x) := Eq.cong (\y => Succ t * y) (Nat.mulComm (smallestPeriod x) n)
        _ = (Succ t * n) * smallestPeriod x := Eq.sym (Nat.mulAssoc (Succ t) n (smallestPeriod x))
        _ = blockCount x * smallestPeriod x := Eq.cong (\y => y * smallestPeriod x) (Eq.sym e)
        _ = digitCount x                    := Eq.sym (countTimesPeriod x)
    let hw: writtenAs (Nat.digits x) k n = True :=
      periodWritten (Nat.digits x) (digitCountNonZero x) k n (Nat.leTrans 1 2 n rfl hn) ekn
        (periodMul (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (smallestPeriod x) (smallestIsPeriod x) (Succ t))
    List.anyRangeIntro (\k => writtenAs (Nat.digits x) k n) (digitCount x) 1 k rfl
      (Nat.leCongRight k (k * n) (digitCount x) ekn (Nat.leMulPos k n (Nat.leTrans 1 2 n rfl hn))) hw

-- x's digits are a block written n times exactly when n divides the block count.
theorem copiesDivides (x: Nat) (n: Nat) (hn: 2 <= n): copies x n = Nat.divides n (blockCount x) :=
  Bool.eqOf (copies x n) (Nat.divides n (blockCount x))
    (\h => List.anyRangeElim (\k => writtenAs (Nat.digits x) k n) (Nat.divides n (blockCount x) = True) (digitCount x) 1 h
      (\k h1 h2 hw => dividesOfWritten x n hn k h1 hw))
    (\h => Nat.dividesElim (copies x n = True) n (blockCount x) h (\t e => writtenOfDivides x n hn t e))

-- x repeats exactly when its smallest block is written at least twice.
theorem repeatsBlocks (x: Nat): repeats x = Nat.leq 2 (blockCount x) :=
  Bool.eqOf (repeats x) (Nat.leq 2 (blockCount x))
    (\h => List.anyRangeElim (\k => List.any (\n => writtenAs (Nat.digits x) k n) (List.rangeFrom (digitCount x) 2)) (2 <= blockCount x) (digitCount x) 1 h
      (\k h1 h2 hk => List.anyRangeElim (\n => writtenAs (Nat.digits x) k n) (2 <= blockCount x) (digitCount x) 2 hk
        (\n n1 n2 hw => Nat.leTrans 2 n (blockCount x) n1
          (Nat.dividesLe n (blockCount x) (blockCountPos x)
            (Eq.trans (Eq.sym (copiesDivides x n n1)) (List.anyRangeIntro (\k => writtenAs (Nat.digits x) k n) (digitCount x) 1 k h1 h2 hw))))))
    (\h => List.anyRangeElim (\k => writtenAs (Nat.digits x) k (blockCount x)) (repeats x = True) (digitCount x) 1
      (Eq.trans (copiesDivides x (blockCount x) h) (Nat.dividesSelf (blockCount x)))
      (\k h1 h2 hw => List.anyRangeIntro (\k => List.any (\n => writtenAs (Nat.digits x) k n) (List.rangeFrom (digitCount x) 2)) (digitCount x) 1 k h1 h2
        (List.anyRangeIntro (\n => writtenAs (Nat.digits x) k n) (digitCount x) 2 (blockCount x) h
          (Nat.leTrans (blockCount x) (digitCount x) (Succ (digitCount x)) (blockCountLe x) (Nat.leSucc (digitCount x))) hw)))

-- One id's terms under weights w: every block length k up to `size` and
-- repeat count n from 2 to `size`.
def idTerms (w: Nat -> Nat) (size: Nat) (x: Nat): Nat :=
  List.rangeFrom size 1 |> .sumBy (\k => List.rangeFrom (size - 1) 2 |> .sumBy (\n => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)))

-- They add up to x times the weights of the divisors of the block count.
theorem idTermsDivisors (w: Nat -> Nat) (size: Nat) (x: Nat) (hL: digitCount x <= size):
    idTerms w size x = x * divisorWeights w (blockCount x) (size - 1) :=
  calc idTerms w size x
    _ = List.sumBy (\n => List.sumBy (\k => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1)) (List.rangeFrom (size - 1) 2)
        := List.sumBySwap (\k n => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom (size - 1) 2) (List.rangeFrom size 1)
    _ = List.sumBy (\n => x * (if Nat.divides n (blockCount x) then w n else 0)) (List.rangeFrom (size - 1) 2)
        := List.sumRangeCongr (\n => List.sumBy (\k => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1))
             (\n => x * (if Nat.divides n (blockCount x) then w n else 0)) (size - 1) 2
             (\n n1 n2 =>
               calc List.sumBy (\k => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1)
                 _ = w n * List.sumBy (\k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1)
                     := List.sumByMulLeft (w n) (\k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1)
                 _ = w n * Nat.keepIf x (copies x n) := Eq.cong (\t => w n * t) (collapse x n n1 size hL)
                 _ = w n * Nat.keepIf x (Nat.divides n (blockCount x)) := Eq.cong (\b => w n * Nat.keepIf x b) (copiesDivides x n n1)
                 _ = x * (if Nat.divides n (blockCount x) then w n else 0) := mulKeep (w n) x (Nat.divides n (blockCount x)))
    _ = x * divisorWeights w (blockCount x) (size - 1)
        := List.sumByMulLeft x (\n => if Nat.divides n (blockCount x) then w n else 0) (List.rangeFrom (size - 1) 2)

-- One id: its plus terms are its minus terms, and x itself if x repeats.
theorem idPlusMinus (size: Nat) (x: Nat) (hL: digitCount x <= size): idTerms plus size x = Nat.keepIf x (repeats x) + idTerms minus size x :=
  let m := blockCount x
  let hc: m <= Succ (size - 1) :=
    Nat.leTrans m size (Succ (size - 1)) (Nat.leTrans m (digitCount x) size (blockCountLe x) hL) (Nat.predLeSucc size (size - 1) (Nat.leRefl (size - 1)))
  calc idTerms plus size x
    _ = x * divisorWeights plus m (size - 1) := idTermsDivisors plus size x hL
    _ = x * divisorWeights plus m (m - 1)    := Eq.cong (\t => x * t) (divisorWeightsAll plus m (blockCountPos x) (size - 1) hc)
    _ = x * (Bool.toNat (Nat.leq 2 m) + divisorWeights minus m (m - 1)) := Eq.cong (\t => x * t) (plusOneMore m (blockCountPos x))
    _ = x * Bool.toNat (Nat.leq 2 m) + x * divisorWeights minus m (m - 1) := Nat.mulDistribLeft x (Bool.toNat (Nat.leq 2 m)) (divisorWeights minus m (m - 1))
    _ = Nat.keepIf x (repeats x) + x * divisorWeights minus m (m - 1)
        := Eq.cong (\t => t + x * divisorWeights minus m (m - 1)) (Eq.trans (Nat.mulToNat x (Nat.leq 2 m)) (Eq.cong (Nat.keepIf x) (Eq.sym (repeatsBlocks x))))
    _ = Nat.keepIf x (repeats x) + x * divisorWeights minus m (size - 1)
        := Eq.cong (\t => Nat.keepIf x (repeats x) + x * t) (Eq.sym (divisorWeightsAll minus m (blockCountPos x) (size - 1) hc))
    _ = Nat.keepIf x (repeats x) + idTerms minus size x := Eq.cong (\t => Nat.keepIf x (repeats x) + t) (Eq.sym (idTermsDivisors minus size x hL))


-- (6) Swapping the sums ------------------------------------------------------

-- A term with more digits than `to` is 0 anyway.
theorem keptTerm (w: Nat -> Nat) (r: Range) (k: Nat) (hk: 1 <= k) (n: Nat) (hn: 2 <= n):
    (if Nat.leq (k * n) (List.length (Nat.digits r.to)) then w n * repeated r k n else 0) = w n * repeated r k n :=
  match h: Nat.leq (k * n) (List.length (Nat.digits r.to)) with
    | True  => rfl
    | False => Eq.sym (Eq.trans (Eq.cong (\t => w n * t) (repeatedZero r k hk n hn h)) (Nat.mulZero (w n)))

-- One term of `weighted`, as a sum over the ids of the range.
theorem termIds (w: Nat -> Nat) (r: Range) (k: Nat) (hk: 1 <= k) (n: Nat) (hn: 2 <= n):
    (if Nat.leq (k * n) (List.length (Nat.digits r.to)) then w n * repeated r k n else 0)
      = List.sumBy (\x => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids :=
  Eq.trans (keptTerm w r k hk n hn)
    (Eq.trans (Eq.cong (\t => w n * t) (repeatedIds r k hk n hn))
      (Eq.sym (List.sumByMulLeft (w n) (\x => Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids)))

-- A block written n times with more digits than `to` adds nothing.
theorem repeatedZero (r: Range) (k: Nat) (hk: 1 <= k) (n: Nat) (hn: 2 <= n) (h: Nat.leq (k * n) (List.length (Nat.digits r.to)) = False): repeated r k n = 0 :=
  Eq.trans (repeatedIds r k hk n hn)
    (List.sumRangeNone (\x => writtenAs (Nat.digits x) k n) (\x => x) r.size r.from
      (\x x1 x2 =>
        match t: writtenAs (Nat.digits x) k n with
          | True =>
            Void.exfalso (Nat.lessIrrefl (List.length (Nat.digits r.to))
              (calc Succ (List.length (Nat.digits r.to))
                _ <= k * n                      := Nat.leqFalse (k * n) (List.length (Nat.digits r.to)) h
                _ = List.length (Nat.digits x)  := Eq.trans (Nat.mulComm k n) (countOf x k n hn t)
                _ <= List.length (Nat.digits r.to) := idsBelow r x x1 x2))
          | False => rfl))

-- One range under weights w, id by id.
theorem weightedIds (w: Nat -> Nat) (r: Range): weighted w r = List.sumBy (\x => idTerms w (List.length (Nat.digits r.to)) x) r.ids :=
  let size := List.length (Nat.digits r.to)
  calc weighted w r
    _ = List.sumBy (\k => List.sumBy (\n => List.sumBy (\x => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids) (List.rangeFrom (size - 1) 2)) (List.rangeFrom size 1)
        := List.sumRangeCongr (\k => List.sumBy (\n => if Nat.leq (k * n) size then w n * repeated r k n else 0) (List.rangeFrom (size - 1) 2))
             (\k => List.sumBy (\n => List.sumBy (\x => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids) (List.rangeFrom (size - 1) 2)) size 1
             (\k k1 k2 => List.sumRangeCongr (\n => if Nat.leq (k * n) size then w n * repeated r k n else 0)
               (\n => List.sumBy (\x => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids) (size - 1) 2
               (\n n1 n2 => termIds w r k k1 n n1))
    _ = List.sumBy (\k => List.sumBy (\x => List.sumBy (\n => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom (size - 1) 2)) r.ids) (List.rangeFrom size 1)
        := List.sumByCongr (\k => List.sumBy (\n => List.sumBy (\x => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids) (List.rangeFrom (size - 1) 2))
             (\k => List.sumBy (\x => List.sumBy (\n => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom (size - 1) 2)) r.ids)
             (\k => List.sumBySwap (\n x => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids (List.rangeFrom (size - 1) 2))
             (List.rangeFrom size 1)
    _ = List.sumBy (\x => idTerms w size x) r.ids
        := List.sumBySwap (\k x => List.sumBy (\n => w n * Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom (size - 1) 2)) r.ids (List.rangeFrom size 1)

-- One range: the plus terms are the puzzle's sum plus the minus terms.
theorem rangeSplit (r: Range): weighted plus r = List.sum (List.filter repeats r.ids) + weighted minus r :=
  let size := List.length (Nat.digits r.to)
  calc weighted plus r
    _ = List.sumBy (\x => idTerms plus size x) r.ids := weightedIds plus r
    _ = List.sumBy (\x => Nat.keepIf x (repeats x) + idTerms minus size x) r.ids
        := List.sumRangeCongr (\x => idTerms plus size x) (\x => Nat.keepIf x (repeats x) + idTerms minus size x) r.size r.from
             (\x x1 x2 => idPlusMinus size x (idsBelow r x x1 x2))
    _ = List.sumBy (\x => Nat.keepIf x (repeats x)) r.ids + List.sumBy (\x => idTerms minus size x) r.ids
        := List.sumByAdd (\x => Nat.keepIf x (repeats x)) (\x => idTerms minus size x) r.ids
    _ = List.sum (List.filter repeats r.ids) + weighted minus r
        := Eq.trans (Eq.cong (\t => t + List.sumBy (\x => idTerms minus size x) r.ids) (Eq.sym (List.sumFilter repeats r.ids)))
             (Eq.cong (\t => List.sum (List.filter repeats r.ids) + t) (Eq.sym (weightedIds minus r)))

theorem invalidCorrect (r: Range): invalid r = List.sum (List.filter repeats r.ids) :=
  Eq.trans (Eq.cong (\t => t - weighted minus r) (rangeSplit r)) (Nat.addSub (List.sum (List.filter repeats r.ids)) (weighted minus r))


-- Part 2 is right -------------------------------------------------------------

-- The puzzle's method: in every range walk the ids, keep those whose digits
-- are some block written two or more times, add them up.
def part2Spec (ranges: List Range): Nat :=
  ranges |> .sumBy (\r => r.ids |> .filter repeats |> .sum)

test "part 2 spec" := part2Spec exampleRanges == 4174379265

-- Part 2 is the sum of the ids, in all the ranges, whose digits are some
-- block written two or more times. For every input.
theorem part2Correct (ranges: List Range): solvePart2 ranges = part2Spec ranges :=
  List.sumByCongr invalid (\r => List.sum (List.filter repeats (Range.ids r))) invalidCorrect ranges
