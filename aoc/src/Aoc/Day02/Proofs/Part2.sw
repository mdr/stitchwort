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
-- - The program weighs the number of copies n by `copiesWeight n`, an `Int`, defined so
--   that over the divisors of K from 2 on the weights add up to 1 when K >= 2
--   (`weightsOne`). So x's terms add up to x itself exactly when x repeats
--   (`idWeight`).
-- - `sumMatchingTemplate` adds the ids of the range whose digits are a block of the
--   template's length written the template's number of copies (`repeatedIds`). The
--   program's sum over the templates is a grid of block lengths and copies
--   (`sumOfIdsWrittenRepeatedlyGrid`); swapping the sums over ids, block lengths and
--   copies finishes it (`weightedIds`, `rangeWeighted`).
--   The signed total is the natural answer embedded, so `Int.toNat` gives it back.

namespace Aoc.Day02.Proofs
import Aoc.Common (Range)
import Aoc.Common.Proofs (rangeEnd)
import Aoc.Day02 (..)
import Aoc.Day02.Tests (exampleRanges)
import Std (Bool, Decidable, Eq, Int, List, Nat, Void)

-- (1) n copies ------------------------------------------------------------
-- The twice* lemmas of Repeated.sw, for any number of copies n >= 2.

-- The digits `p` written n times make `fromDigits p` written n times.
theorem fromDigitsRep (p: List Nat): (n: Nat) -> Nat.fromDigits (List.concat (List.replicate n p)) = writeTimes p.length (Nat.fromDigits p) n
  | Zero   => rfl
  | Succ n =>
    calc Nat.fromDigits (List.concat (List.replicate (Succ n) p))
      _ = Nat.fromDigits (List.append (List.concat (List.replicate n p)) p) := Eq.cong Nat.fromDigits (List.concatReplicateSnoc p n)
      _ = Nat.fromDigits (List.concat (List.replicate n p)) * Nat.pow 10 p.length + Nat.fromDigits p := Nat.fromDigitsAppend (List.concat (List.replicate n p)) p
      _ = writeTimes p.length (Nat.fromDigits p) n * Nat.pow 10 p.length + Nat.fromDigits p := rewrite fromDigitsRep p n

theorem repAppend (x: Nat) (k: Nat) (n: Nat) (hq: writtenAs (Nat.digits x) k n = True):
    List.concat (List.replicate n (List.take k (Nat.digits x))) = Nat.digits x :=
  Decidable.toBoolSound (List.decEq (a b => Nat.decEq a b) (List.concat (List.replicate n (List.take k (Nat.digits x)))) (Nat.digits x)) hq

-- With two or more copies the block is k digits long (it can't be all of x).
theorem repBlockLength (x: Nat) (k: Nat) (m: Nat) (hq: writtenAs (Nat.digits x) k (Succ (Succ m)) = True): List.length (List.take k (Nat.digits x)) = k :=
  match e: Nat.leq k (List.length (Nat.digits x)) with
    | True  => List.lengthTake k (Nat.digits x) e
    | False => Void.exfalso (Nat.lessIrrefl (List.length (Nat.digits x))
      (calc Succ (List.length (Nat.digits x))
        _ <= List.length (Nat.digits x) + List.length (Nat.digits x) := Nat.leCongLeft (List.length (Nat.digits x) + 1) (Succ (List.length (Nat.digits x))) (List.length (Nat.digits x) + List.length (Nat.digits x)) (Nat.addOne (List.length (Nat.digits x))) (Nat.leAddCong (List.length (Nat.digits x)) 1 (List.length (Nat.digits x)) (Nat.digitsNonEmpty x))
        _ <= List.length (Nat.digits x) + (List.length (Nat.digits x) + List.length (List.concat (List.replicate m (Nat.digits x)))) := Nat.leAddCong (List.length (Nat.digits x)) (List.length (Nat.digits x)) (List.length (Nat.digits x) + List.length (List.concat (List.replicate m (Nat.digits x)))) (Nat.leAddRight (List.length (Nat.digits x)) (List.length (List.concat (List.replicate m (Nat.digits x)))))
        _ = List.length (List.concat (List.replicate (Succ (Succ m)) (Nat.digits x))) := Eq.sym (Eq.trans (List.lengthAppend (Nat.digits x) (List.append (Nat.digits x) (List.concat (List.replicate m (Nat.digits x))))) (Eq.cong (t => List.length (Nat.digits x) + t) (List.lengthAppend (Nat.digits x) (List.concat (List.replicate m (Nat.digits x))))))
        _ = List.length (List.concat (List.replicate (Succ (Succ m)) (List.take k (Nat.digits x)))) := Eq.cong (l => List.length (List.concat (List.replicate (Succ (Succ m)) l))) (Eq.sym (List.takeAll k (Nat.digits x) (Nat.lessLe (List.length (Nat.digits x)) k (Nat.leqFalse k (List.length (Nat.digits x)) e))))
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
    _ = writeTimes (List.length (List.take k (Nat.digits x))) (Nat.fromDigits (List.take k (Nat.digits x))) (Succ (Succ m)) := Eq.cong (t => writeTimes t (Nat.fromDigits (List.take k (Nat.digits x))) (Succ (Succ m))) (Eq.sym (repBlockLength x k m hq))
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
  J (t q => Nat.pow 10 (t - 1) <= Nat.fromDigits (List.take k (Nat.digits x)))
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

theorem writtenRepOf (p: List Nat) (k: Nat) (hk: p.length = k) (n: Nat): writtenAs (List.concat (List.replicate (Succ n) p)) k (Succ n) = True :=
  Decidable.toBoolOf (List.decEq (a b => Nat.decEq a b) (List.concat (List.replicate (Succ n) (List.take k (List.concat (List.replicate (Succ n) p))))) (List.concat (List.replicate (Succ n) p)))
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
    List.sumBy (b => Nat.keepIf x (writeTimes k b (Succ (Succ m)) == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
      = Nat.keepIf x (writtenAs (Nat.digits x) k (Succ (Succ m)))
  | Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ j, h =>
    match hq: writtenAs (Nat.digits x) (Succ j) (Succ (Succ m)) with
      | True =>
        List.sumRangeOne (b => writeTimes (Succ j) b (Succ (Succ m)) == x) (b => x) (Nat.fromDigits (List.take (Succ j) (Nat.digits x)))
          (Decidable.toBoolOf (Nat.decEq (writeTimes (Succ j) (Nat.fromDigits (List.take (Succ j) (Nat.digits x))) (Succ (Succ m))) x) (repValue x (Succ j) m hq))
          (b hb => repInjective (Succ j) b (Nat.fromDigits (List.take (Succ j) (Nat.digits x))) (Succ m)
            (Eq.trans (Decidable.toBoolSound (Nat.decEq (writeTimes (Succ j) b (Succ (Succ m))) x) hb) (Eq.sym (repValue x (Succ j) m hq))))
          (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
          (repAbove x (Succ j) m rfl hq)
          (calc Nat.fromDigits (List.take (Succ j) (Nat.digits x))
            _ < Nat.pow 10 (Succ j)                                  := repBelow x (Succ j) m hq
            _ = Nat.pow 10 j + (Nat.pow 10 (Succ j) - Nat.pow 10 j) := Eq.sym (Nat.addSubCancel (Nat.pow 10 j) (Nat.pow 10 (Succ j)) (Nat.powTenPredLe (Succ j))))
      | False =>
        List.sumRangeNone (b => writeTimes (Succ j) b (Succ (Succ m)) == x) (b => x) (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
          (b h1 h2 => Decidable.toBoolOfNot (Nat.decEq (writeTimes (Succ j) b (Succ (Succ m))) x)
            (e => Bool.trueNotFalse (Eq.trans
              (Eq.sym (rewrite e at
                repDigits j b h1
                  (calc b
                    _ < Nat.pow 10 j + (Nat.pow 10 (Succ j) - Nat.pow 10 j) := h2
                    _ = Nat.pow 10 (Succ j) := Nat.addSubCancel (Nat.pow 10 j) (Nat.pow 10 (Succ j)) (Nat.powTenPredLe (Succ j)))
                  (Succ m)))
              hq)))

-- One block length, as a sum over the ids of the range (`blocksAsIds` for any n).
theorem blocksAsIdsRep (r: Range) (k: Nat) (n: Nat):
    repeatedSpec r k n
      = List.sumBy (x => List.sumBy (b => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
          (List.rangeFrom (r.to + 1 - r.from) r.from) :=
  calc repeatedSpec r k n
    -- filtering the block ids by the range is summing "the id if it is in the range"
    _ = List.sumBy (y => Nat.keepIf y (r.from <= y && y <= r.to)) (List.map (b => writeTimes k b n) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
        := List.sumFilter (x => r.from <= x && x <= r.to) (List.map (b => writeTimes k b n) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
    _ = List.sumBy (b => Nat.keepIf (writeTimes k b n) (r.from <= writeTimes k b n && writeTimes k b n <= r.to)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
        := List.sumByMap (y => Nat.keepIf y (r.from <= y && y <= r.to)) (b => writeTimes k b n) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
    -- and, for each block, "the id if it is in the range" is the sum over the range ids that equal it
    _ = List.sumBy (b => List.sumBy (x => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (r.to + 1 - r.from) r.from)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
        := List.sumByCong (b => Nat.keepIf (writeTimes k b n) (r.from <= writeTimes k b n && writeTimes k b n <= r.to))
             (b => List.sumBy (x => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (r.to + 1 - r.from) r.from))
             (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
             (b => Eq.sym (sumIdsEq r.from r.to (writeTimes k b n)))
    _ = List.sumBy (x => List.sumBy (b => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))) (List.rangeFrom (r.to + 1 - r.from) r.from)
        := List.sumBySwap (b x => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (r.to + 1 - r.from) r.from) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))

-- (1) `sumMatchingTemplate r` of the template k by n adds the ids of the range whose digits are a k-digit
-- block written n times.
theorem repeatedIds (r: Range) (k: Nat) (hk: 1 <= k): (n: Nat) -> 2 <= n ->
    sumMatchingTemplate r { blockLength = k, copies = n } = List.sumBy (x => Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids
  | Zero,          h => Void.exfalso (Bool.falseNotTrue h)
  | Succ Zero,     h => Void.exfalso (Bool.falseNotTrue h)
  | Succ (Succ m), h =>
    calc sumMatchingTemplate r { blockLength = k, copies = Succ (Succ m) }
      _ = repeatedSpec r k (Succ (Succ m)) := repeatedCorrect r k (Succ (Succ m))
      _ = List.sumBy (x => List.sumBy (b => Nat.keepIf x (writeTimes k b (Succ (Succ m)) == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))) r.ids
          := blocksAsIdsRep r k (Succ (Succ m))
      _ = List.sumBy (x => Nat.keepIf x (writtenAs (Nat.digits x) k (Succ (Succ m)))) r.ids
          := List.sumByCong (x => List.sumBy (b => Nat.keepIf x (writeTimes k b (Succ (Succ m)) == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
               (x => Nat.keepIf x (writtenAs (Nat.digits x) k (Succ (Succ m)))) r.ids (x => blockCountRep x m k hk)

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
  List.rangeFrom (Nat.digits x).length 1 |> .any (k => writtenAs (Nat.digits x) k n)

-- For one id and repeat count, over all block lengths up to `size`: x if
-- some block written n times makes x, else 0.
theorem collapse (x: Nat) (n: Nat) (hn: 2 <= n) (size: Nat) (hLS: List.length (Nat.digits x) <= size):
    List.sumBy (k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1) = Nat.keepIf x (copies x n) :=
  match hc: copies x n with
    | True =>
      List.anyRangeElim (k => writtenAs (Nat.digits x) k n) (List.sumBy (k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1) = x) (List.length (Nat.digits x)) 1 hc
        (k0 h1 h2 hk0 => List.sumRangeOne (k => writtenAs (Nat.digits x) k n) (k => x) k0 hk0
          (k hk => Nat.mulCancelLeft n (Nat.leTrans 1 2 n rfl hn) k k0 (Eq.trans (countOf x k n hn hk) (Eq.sym (countOf x k0 n hn hk0))))
          size 1 h1 (Nat.leTrans (Succ k0) (Succ (List.length (Nat.digits x))) (Succ size) h2 hLS))
    | False =>
      List.sumRangeNone (k => writtenAs (Nat.digits x) k n) (k => x) size 1
        (k h1 h2 =>
          match t: writtenAs (Nat.digits x) k n with
            | True  => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (List.anyRangeIntro (k => writtenAs (Nat.digits x) k n) (List.length (Nat.digits x)) 1 k h1 (blockAtMost x k n hn t) t)) hc))
            | False => rfl)

-- The ids of a range have at most as many digits as its end.
theorem idsBelow (r: Range) (x: Nat) (h1: r.from <= x) (h2: x < r.from + r.size): List.length (Nat.digits x) <= List.length (Nat.digits r.to) :=
  Nat.digitsLengthLe x (List.length (Nat.digits r.to)) (Nat.digitsNonEmpty r.to)
    (Nat.leTrans (Succ x) (Succ r.to) (Nat.pow 10 (List.length (Nat.digits r.to))) (rangeEnd r.from r.to x h1 h2) (Nat.ltPowTenDigits r.to))


-- (2) The weights ------------------------------------------------------------
-- Over the divisors of m from 2 on, `copiesWeight` adds up to 1 when m >= 2, and to
-- 0 when m = 1 (`weightsOne`).

-- The weights w of the divisors of m among 2, 3, ..., c + 1, added up.
def divisorWeights (w: Nat -> Int) (m: Nat) (c: Nat): Int :=
  List.rangeFrom c 2 |> .sumBy (d => if Nat.divides d m then w d else 0)

-- A guard that holds takes the first branch.
theorem guardHolds [p: Prop] [a: Type]: (d: Decidable p) -> p -> (x: a) -> (y: a) -> Decidable.elim d (g => x) (r => y) = x
  | Yes q, h, x, y => rfl
  | No r,  h, x, y => Void.exfalso (r h)

-- The weight of m = j + 2 is 1, less the weights of its divisors below m
-- (`weight.unfold`, with the guard `d < m` discharged for each d of the run).
theorem weightBelow (j: Nat): copiesWeight (Succ (Succ j)) = 1 - divisorWeights copiesWeight (Succ (Succ j)) j :=
  let guarded: Nat -> Int := d => if h: d < Succ (Succ j) then (if Nat.divides d (Succ (Succ j)) then copiesWeight d else 0) else 0
  let plain: Nat -> Int := d => if Nat.divides d (Succ (Succ j)) then copiesWeight d else 0
  calc copiesWeight (Succ (Succ j))
    _ = 1 - List.sumBy guarded (List.rangeFrom j 2) := copiesWeight.unfold (Succ (Succ j))
    _ = 1 - List.sumBy plain (List.rangeFrom j 2)
        := Eq.cong (Int.sub 1)
             (List.sumRangeCongr guarded plain j 2
               (d d1 d2 => guardHolds (Nat.decLessThan d (Succ (Succ j))) d2 (plain d) 0))

theorem divisorWeightsTop (w: Nat -> Int) (j: Nat): divisorWeights w (Succ (Succ j)) (Succ j) = divisorWeights w (Succ (Succ j)) j + w (Succ (Succ j)) :=
  let f: Nat -> Int := d => if Nat.divides d (Succ (Succ j)) then w d else 0
  calc List.sumBy f (List.rangeFrom (Succ j) 2)
    _ = List.sumBy f (List.rangeFrom (j + 1) 2) := Eq.cong (t => List.sumBy f (List.rangeFrom t 2)) (Eq.sym (Nat.addOne j))
    _ = List.sumBy f (List.append (List.rangeFrom j 2) (List.rangeFrom 1 (2 + j))) := Eq.cong (List.sumBy f) (List.rangeFromAppend j 1 2)
    _ = List.sumBy f (List.rangeFrom j 2) + List.sumBy f (List.rangeFrom 1 (2 + j)) := List.sumByAppend f (List.rangeFrom j 2) (List.rangeFrom 1 (2 + j))
    _ = List.sumBy f (List.rangeFrom j 2) + f (Succ (Succ j))
        := Eq.cong (t => List.sumBy f (List.rangeFrom j 2) + t) (Int.zeroAdd (f (Succ (Succ j))))
    _ = List.sumBy f (List.rangeFrom j 2) + w (Succ (Succ j))
        := Eq.cong (c => List.sumBy f (List.rangeFrom j 2) + (if c then w (Succ (Succ j)) else 0)) (Nat.dividesSelf (Succ (Succ j)))

-- The key fact: the weights of the divisors of m from 2 on add up to 1.
theorem weightsOne: (m: Nat) -> 1 <= m -> divisorWeights copiesWeight m (m - 1) = (Bool.toNat (Nat.leq 2 m)).toInt
  | Zero,          h => Void.exfalso (Bool.falseNotTrue h)
  | Succ Zero,     h => rfl
  | Succ (Succ j), h =>
    calc divisorWeights copiesWeight (Succ (Succ j)) (Succ j)
      _ = divisorWeights copiesWeight (Succ (Succ j)) j + copiesWeight (Succ (Succ j)) := divisorWeightsTop copiesWeight j
      _ = divisorWeights copiesWeight (Succ (Succ j)) j + (1 - divisorWeights copiesWeight (Succ (Succ j)) j)
          := Eq.cong (t => divisorWeights copiesWeight (Succ (Succ j)) j + t) (weightBelow j)
      _ = 1 := Int.addSubCancel (divisorWeights copiesWeight (Succ (Succ j)) j) 1

-- Divisors of m beyond m count for nothing.
theorem divisorWeightsAll (w: Nat -> Int): (m: Nat) -> 1 <= m -> (c: Nat) -> m <= Succ c -> divisorWeights w m c = divisorWeights w m (m - 1)
  | Zero,   hm, c, hc => Void.exfalso (Bool.falseNotTrue hm)
  | Succ k, hm, c, hc =>
    let f: Nat -> Int := d => if Nat.divides d (Succ k) then w d else 0
    calc List.sumBy f (List.rangeFrom c 2)
      _ = List.sumBy f (List.rangeFrom (k + (c - k)) 2) := Eq.cong (t => List.sumBy f (List.rangeFrom t 2)) (Eq.sym (Nat.addSubCancel k c hc))
      _ = List.sumBy f (List.append (List.rangeFrom k 2) (List.rangeFrom (c - k) (2 + k))) := Eq.cong (List.sumBy f) (List.rangeFromAppend k (c - k) 2)
      _ = List.sumBy f (List.rangeFrom k 2) + List.sumBy f (List.rangeFrom (c - k) (2 + k)) := List.sumByAppend f (List.rangeFrom k 2) (List.rangeFrom (c - k) (2 + k))
      _ = List.sumBy f (List.rangeFrom k 2) + 0
          := Eq.cong (t => List.sumBy f (List.rangeFrom k 2) + t)
               (Eq.trans (List.sumRangeCongr f (d => 0) (c - k) (2 + k)
                   (d d1 d2 => Eq.cong (b => if b then w d else 0) (Nat.dividesSmall d (Succ k) rfl d1)))
                 (List.sumByZero [add := Int.instAdd] (List.rangeFrom (c - k) (2 + k))))
      _ = List.sumBy f (List.rangeFrom k 2) := Int.addZero (List.sumBy f (List.rangeFrom k 2))

theorem mulKeep (v: Int) (x: Nat): (b: Bool) -> v * (Nat.keepIf x b).toInt = x.toInt * (if b then v else 0)
  | True  => Int.mulComm v x.toInt
  | False => Eq.trans (Int.mulZero v) (Eq.sym (Int.mulZero x.toInt))


-- (3) Periods ----------------------------------------------------------------

-- Rotating the first `len` values of g by p places leaves them unchanged.
def Period (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat): Prop := (i: Nat) -> i < len -> g ((i + p) % len) = g i

theorem periodZero (g: Nat -> Nat) (len: Nat) (hl: len != 0): Period g len hl 0 :=
  i hi => Eq.cong g (Eq.trans (Eq.cong (y => y % len) (Nat.addZero i)) (Nat.modSmall i len hi))

theorem periodLen (g: Nat -> Nat) (len: Nat) (hl: len != 0): Period g len hl len :=
  i hi => Eq.cong g (Eq.trans (Eq.cong (y => y % len) (Nat.addComm i len)) (Eq.trans (Nat.addModSelf len i) (Nat.modSmall i len hi)))

-- Doing one rotation and then the other is a rotation too.
theorem periodAdd (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat) (q: Nat) (hp: Period g len hl p) (hq: Period g len hl q): Period g len hl (p + q) :=
  i hi =>
    calc g ((i + (p + q)) % len)
      _ = g (((i + p) + q) % len)       := Eq.cong (y => g (y % len)) (Eq.sym (Nat.addAssoc i p q))
      _ = g (((i + p) % len + q) % len) := Eq.cong g (Eq.sym (Nat.modAddMod (i + p) q len))
      _ = g ((i + p) % len)             := hq ((i + p) % len) (Nat.modLess (i + p) len hl)
      _ = g i                           := hp i hi

theorem periodSub (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat) (q: Nat) (hp: Period g len hl p) (hq: Period g len hl q) (hle: q <= p): Period g len hl (p - q) :=
  i hi =>
    calc g ((i + (p - q)) % len)
      _ = g (((i + (p - q)) % len + q) % len) := Eq.sym (hq ((i + (p - q)) % len) (Nat.modLess (i + (p - q)) len hl))
      _ = g ((i + (p - q) + q) % len)         := Eq.cong g (Nat.modAddMod (i + (p - q)) q len)
      _ = g ((i + p) % len)
          := Eq.cong (y => g (y % len)) (Eq.trans (Nat.addAssoc i (p - q) q) (Eq.cong (t => i + t) (Eq.trans (Nat.addComm (p - q) q) (Nat.addSubCancel q p hle))))
      _ = g i                                 := hp i hi

theorem periodMul (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat) (hp: Period g len hl p): (t: Nat) -> Period g len hl (t * p)
  | Zero,   i, hi => periodZero g len hl i hi
  | Succ t, i, hi => periodAdd g len hl p (t * p) hp (j hj => periodMul g len hl p hp t j hj) i hi

-- The same as a test, which a search can run.
def isPeriod (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat): Bool := List.range len |> .all (i => g ((i + p) % len) == g i)

theorem periodOfTest (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat) (h: isPeriod g len hl p = True): Period g len hl p :=
  i hi => Decidable.toBoolSound (Nat.decEq (g ((i + p) % len)) (g i)) (List.allRangeElim (i => g ((i + p) % len) == g i) len 0 h i (Nat.zeroLe i) hi)

theorem periodTest (g: Nat -> Nat) (len: Nat) (hl: len != 0) (p: Nat) (h: Period g len hl p): isPeriod g len hl p = True :=
  List.allRangeIntro (i => g ((i + p) % len) == g i) len 0 (i h1 h2 => Decidable.toBoolOf (Nat.decEq (g ((i + p) % len)) (g i)) (h i h2))

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
    Eq.trans (Eq.cong (y => y - t * Succ j) (Eq.trans (Nat.divModEq p (Succ j) (Nat.succNotZero j)) (Nat.addComm (t * Succ j) (p % Succ j))))
      (Nat.addSub (p % Succ j) (t * Succ j))
  periodBelow g len hl j hmin (p % Succ j) (rewrite e at rest) (Nat.modLess p (Succ j) (Nat.succNotZero j))


-- (4) Blocks are periods -----------------------------------------------------

-- The digit at position i (0 past the end).
def digitAt (ds: List Nat) (i: Nat): Nat := List.getOr 0 i ds

-- Digits that are their first k digits written n times: each digit is the
-- one at its position within the first k.
theorem writtenBlock (ds: List Nat) (k: Nat) (n: Nat) [auto hk: k != 0] (hn: 1 <= n) (e: k * n = ds.length) (hw: writtenAs ds k n = True)
    (j: Nat) (hj: j < ds.length): digitAt ds j = digitAt ds (j % k) :=
  calc List.getOr 0 j ds
    _ = List.getOr 0 j (List.concat (List.replicate n (List.take k ds)))
        := Eq.cong (l => List.getOr 0 j l) (Eq.sym (Decidable.toBoolSound (List.decEq (a b => Nat.decEq a b) (List.concat (List.replicate n (List.take k ds))) ds) hw))
    _ = List.getOr 0 (j % k) (List.take k ds)
        := List.getOrConcatReplicate 0 (List.take k ds) k (List.lengthTake k ds (Nat.leCongRight k (k * n) ds.length e (Nat.leMulPos k n hn))) n j
             (Nat.ltCongRight j ds.length (n * k) (Eq.trans (Eq.sym e) (Nat.mulComm k n)) hj)
    _ = List.getOr 0 (j % k) ds := List.getOrTake 0 k (j % k) ds (Nat.modLess j k hk)

theorem writtenPeriod (ds: List Nat) (hl: ds.length != 0) (k: Nat) (n: Nat) [auto hk: k != 0] (hn: 1 <= n) (e: k * n = ds.length)
    (hw: writtenAs ds k n = True): Period (digitAt ds) ds.length hl k :=
  i hi =>
    calc digitAt ds ((i + k) % ds.length)
      _ = digitAt ds ((i + k) % ds.length % k) := writtenBlock ds k n hn e hw ((i + k) % ds.length) (Nat.modLess (i + k) ds.length hl)
      _ = digitAt ds ((i + k) % k)                  := Eq.cong (digitAt ds) (Nat.modModOfMul (i + k) ds.length k n (Eq.trans (Eq.sym e) (Nat.mulComm k n)))
      _ = digitAt ds (i % k)                        := Eq.cong (digitAt ds) (Eq.trans (Eq.cong (y => y % k) (Nat.addComm i k)) (Nat.addModSelf k i))
      _ = digitAt ds i                              := Eq.sym (writtenBlock ds k n hn e hw i hi)

-- With period k, each digit is the one at its position within the first k.
theorem periodBlock (ds: List Nat) (hl: ds.length != 0) (k: Nat) [auto hk: k != 0] (hp: Period (digitAt ds) ds.length hl k)
    (i: Nat) (hi: i < ds.length): digitAt ds i = digitAt ds (i % k) :=
  calc digitAt ds i
    _ = digitAt ds (i % ds.length)                     := Eq.cong (digitAt ds) (Eq.sym (Nat.modSmall i ds.length hi))
    _ = digitAt ds ((i % k + (i / k) * k) % ds.length)
        := Eq.cong (y => digitAt ds (y % ds.length)) (Eq.trans (Nat.divModEq i k hk) (Nat.addComm ((i / k) * k) (i % k)))
    _ = digitAt ds (i % k)
        := periodMul (digitAt ds) ds.length hl k hp (i / k) (i % k) (Nat.leTrans (Succ (i % k)) (Succ i) ds.length (Nat.subLe i ((i / k) * k)) hi)

theorem periodWritten (ds: List Nat) (hl: ds.length != 0) (k: Nat) (n: Nat) [auto hk: k != 0] (hn: 1 <= n) (e: k * n = ds.length)
    (hp: Period (digitAt ds) ds.length hl k): writtenAs ds k n = True :=
  let ht: List.length (List.take k ds) = k := List.lengthTake k ds (Nat.leCongRight k (k * n) ds.length e (Nat.leMulPos k n hn))
  let len: List.length (List.concat (List.replicate n (List.take k ds))) = n * k :=
    Eq.trans (List.lengthConcatReplicate (List.take k ds) n) (Eq.cong (t => n * t) ht)
  Decidable.toBoolOf (List.decEq (a b => Nat.decEq a b) (List.concat (List.replicate n (List.take k ds))) ds)
    (List.extGetOr 0 (List.concat (List.replicate n (List.take k ds))) ds (Eq.trans len (Eq.trans (Nat.mulComm n k) e))
      (i hi =>
        calc List.getOr 0 i (List.concat (List.replicate n (List.take k ds)))
          _ = List.getOr 0 (i % k) (List.take k ds) := List.getOrConcatReplicate 0 (List.take k ds) k ht n i (Nat.ltCongRight i (List.length (List.concat (List.replicate n (List.take k ds)))) (n * k) len hi)
          _ = List.getOr 0 (i % k) ds               := List.getOrTake 0 k (i % k) ds (Nat.modLess i k hk)
          _ = List.getOr 0 i ds
              := Eq.sym (periodBlock ds hl k hp i (Nat.ltCongRight i (n * k) ds.length (Eq.trans (Nat.mulComm n k) e) (Nat.ltCongRight i (List.length (List.concat (List.replicate n (List.take k ds)))) (n * k) len hi)))))


-- (5) One id -----------------------------------------------------------------

def digitCount (x: Nat): Nat := List.length (Nat.digits x)

theorem digitCountNonZero (x: Nat): digitCount x != 0 := Nat.nonzeroOfPos (digitCount x) (Nat.digitsNonEmpty x)

-- x's digits have period p.
def periodOf (x: Nat) (p: Nat): Bool := isPeriod (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) p

-- x's smallest positive period is `Succ (periodIndex x)`: the first p in
-- 1, 2, ..., digitCount x that passes (the digit count always does).
def periodIndex (x: Nat): Nat := Nat.firstFrom (j => periodOf x (Succ j)) (digitCount x) 0

def smallestPeriod (x: Nat): Nat := Succ (periodIndex x)

-- How many times x's smallest block is written.
def blockCount (x: Nat): Nat := digitCount x / smallestPeriod x

test "smallest blocks" := List.map blockCount [7, 1212, 123123123, 1213] == [1, 2, 3, 1]

theorem smallestIsPeriod (x: Nat): Period (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (smallestPeriod x) :=
  let top: Succ (digitCount x - 1) = digitCount x := Nat.addSubCancel 1 (digitCount x) (Nat.digitsNonEmpty x)
  periodOfTest (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (smallestPeriod x)
    (Nat.firstFromFound (j => periodOf x (Succ j)) (digitCount x) 0 (digitCount x - 1) (Nat.zeroLe (digitCount x - 1))
      (Nat.leCongLeft (digitCount x) (Succ (digitCount x - 1)) (digitCount x) (Eq.sym top) (Nat.leRefl (digitCount x)))
      (rewrite top in periodTest (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (digitCount x) (periodLen (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x))))

theorem smallestDivides (x: Nat) (p: Nat) (hp: Period (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) p): p % smallestPeriod x = 0 :=
  periodDvd (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (periodIndex x) (smallestIsPeriod x)
    (r hr => Nat.firstFromBefore (j => periodOf x (Succ j)) (digitCount x) 0 r (Nat.zeroLe r) hr) p hp

theorem countTimesPeriod (x: Nat): digitCount x = blockCount x * smallestPeriod x :=
  calc digitCount x
    _ = blockCount x * smallestPeriod x + digitCount x % smallestPeriod x := Nat.divModEq (digitCount x) (smallestPeriod x) (Nat.succNotZero (periodIndex x))
    _ = blockCount x * smallestPeriod x + 0
        := Eq.cong (t => blockCount x * smallestPeriod x + t)
             (smallestDivides x (digitCount x) (periodLen (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x)))
    _ = blockCount x * smallestPeriod x := Nat.addZero (blockCount x * smallestPeriod x)

theorem blockCountPos (x: Nat): 1 <= blockCount x :=
  match e: blockCount x with
    | Zero   => Void.exfalso (Bool.falseNotTrue (rewrite countTimesPeriod x, e at (Nat.digitsNonEmpty x: 1 <= digitCount x)))
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
    Eq.trans (Nat.divModEq k (smallestPeriod x) (Nat.succNotZero (periodIndex x)))
      (Eq.trans (Eq.cong (r => t * smallestPeriod x + r) (smallestDivides x k per)) (Nat.addZero (t * smallestPeriod x)))
  let eK: blockCount x = n * t :=
    Nat.mulSuccCancel (blockCount x) (n * t) (periodIndex x)
      (calc blockCount x * smallestPeriod x
        _ = digitCount x                   := Eq.sym (countTimesPeriod x)
        _ = n * k                          := Eq.sym (countOf x k n hn hw)
        _ = n * (t * smallestPeriod x)     := Eq.cong (y => n * y) ek
        _ = n * t * smallestPeriod x       := Eq.sym (Nat.mulAssoc n t (smallestPeriod x)))
  rewrite <- Nat.mulComm n t, <- eK at Nat.dividesMul n t

-- And back: if n divides the block count, the digits are a block written n times.
theorem writtenOfDivides (x: Nat) (n: Nat) (hn: 2 <= n): (t: Nat) -> blockCount x = t * n -> copies x n = True
  | Zero,   e => Void.exfalso (Bool.falseNotTrue (rewrite e at blockCountPos x))
  | Succ t, e =>
    let k := Succ t * smallestPeriod x
    let ekn: k * n = digitCount x :=
      calc (Succ t * smallestPeriod x) * n
        _ = Succ t * (smallestPeriod x * n) := Nat.mulAssoc (Succ t) (smallestPeriod x) n
        _ = Succ t * (n * smallestPeriod x) := Eq.cong (y => Succ t * y) (Nat.mulComm (smallestPeriod x) n)
        _ = (Succ t * n) * smallestPeriod x := Eq.sym (Nat.mulAssoc (Succ t) n (smallestPeriod x))
        _ = blockCount x * smallestPeriod x := Eq.cong (y => y * smallestPeriod x) (Eq.sym e)
        _ = digitCount x                    := Eq.sym (countTimesPeriod x)
    let hw: writtenAs (Nat.digits x) k n = True :=
      periodWritten (Nat.digits x) (digitCountNonZero x) k n (Nat.leTrans 1 2 n rfl hn) ekn
        (periodMul (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (smallestPeriod x) (smallestIsPeriod x) (Succ t))
    List.anyRangeIntro (k => writtenAs (Nat.digits x) k n) (digitCount x) 1 k rfl
      (Nat.leCongRight k (k * n) (digitCount x) ekn (Nat.leMulPos k n (Nat.leTrans 1 2 n rfl hn))) hw

-- x's digits are a block written n times exactly when n divides the block count.
theorem copiesDivides (x: Nat) (n: Nat) (hn: 2 <= n): copies x n = Nat.divides n (blockCount x) :=
  Bool.eqOf (copies x n) (Nat.divides n (blockCount x))
    (h => List.anyRangeElim (k => writtenAs (Nat.digits x) k n) (Nat.divides n (blockCount x) = True) (digitCount x) 1 h
      (k h1 h2 hw => dividesOfWritten x n hn k h1 hw))
    (h => Nat.dividesElim (copies x n = True) n (blockCount x) h (t e => writtenOfDivides x n hn t e))

-- x repeats exactly when its smallest block is written at least twice.
theorem repeatsBlocks (x: Nat): repeats x = Nat.leq 2 (blockCount x) :=
  Bool.eqOf (repeats x) (Nat.leq 2 (blockCount x))
    (h => List.anyRangeElim (k => List.any (n => writtenAs (Nat.digits x) k n) (List.rangeFrom (digitCount x) 2)) (2 <= blockCount x) (digitCount x) 1 h
      (k h1 h2 hk => List.anyRangeElim (n => writtenAs (Nat.digits x) k n) (2 <= blockCount x) (digitCount x) 2 hk
        (n n1 n2 hw => Nat.leTrans 2 n (blockCount x) n1
          (Nat.dividesLe n (blockCount x) (blockCountPos x)
            (Eq.trans (Eq.sym (copiesDivides x n n1)) (List.anyRangeIntro (k => writtenAs (Nat.digits x) k n) (digitCount x) 1 k h1 h2 hw))))))
    (h => List.anyRangeElim (k => writtenAs (Nat.digits x) k (blockCount x)) (repeats x = True) (digitCount x) 1
      (Eq.trans (copiesDivides x (blockCount x) h) (Nat.dividesSelf (blockCount x)))
      (k h1 h2 hw => List.anyRangeIntro (k => List.any (n => writtenAs (Nat.digits x) k n) (List.rangeFrom (digitCount x) 2)) (digitCount x) 1 k h1 h2
        (List.anyRangeIntro (n => writtenAs (Nat.digits x) k n) (digitCount x) 2 (blockCount x) h
          (Nat.leTrans (blockCount x) (digitCount x) (Succ (digitCount x)) (blockCountLe x) (Nat.leSucc (digitCount x))) hw)))

-- One id's terms under weights w: every block length k up to `size` and
-- repeat count n from 2 to `size`.
def idTerms (w: Nat -> Int) (size: Nat) (x: Nat): Int :=
  List.rangeFrom size 1 |> .sumBy (k => List.rangeFrom (size - 1) 2 |> .sumBy (n => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt))

-- They add up to x times the weights of the divisors of the block count.
theorem idTermsDivisors (w: Nat -> Int) (size: Nat) (x: Nat) (hL: digitCount x <= size):
    idTerms w size x = x.toInt * divisorWeights w (blockCount x) (size - 1) :=
  calc idTerms w size x
    _ = List.sumBy (n => List.sumBy (k => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) (List.rangeFrom size 1)) (List.rangeFrom (size - 1) 2)
        := List.sumBySwap (k n => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) (List.rangeFrom (size - 1) 2) (List.rangeFrom size 1)
    _ = List.sumBy (n => x.toInt * (if Nat.divides n (blockCount x) then w n else 0)) (List.rangeFrom (size - 1) 2)
        := List.sumRangeCongr (n => List.sumBy (k => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) (List.rangeFrom size 1))
             (n => x.toInt * (if Nat.divides n (blockCount x) then w n else 0)) (size - 1) 2
             (n n1 n2 =>
               calc List.sumBy (k => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) (List.rangeFrom size 1)
                 _ = w n * List.sumBy (k => (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) (List.rangeFrom size 1)
                     := Int.sumByMulLeft (w n) (k => (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) (List.rangeFrom size 1)
                 _ = w n * (List.sumBy (k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1)).toInt
                     := Eq.cong (t => w n * t) (Eq.sym (Int.toIntSumBy (k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1)))
                 _ = w n * (Nat.keepIf x (copies x n)).toInt := Eq.cong (t => w n * t.toInt) (collapse x n n1 size hL)
                 _ = w n * (Nat.keepIf x (Nat.divides n (blockCount x))).toInt := Eq.cong (b => w n * (Nat.keepIf x b).toInt) (copiesDivides x n n1)
                 _ = x.toInt * (if Nat.divides n (blockCount x) then w n else 0) := mulKeep (w n) x (Nat.divides n (blockCount x)))
    _ = x.toInt * divisorWeights w (blockCount x) (size - 1)
        := Int.sumByMulLeft x.toInt (n => if Nat.divides n (blockCount x) then w n else 0) (List.rangeFrom (size - 1) 2)

-- One id: its terms add up to x itself if x repeats, and to nothing if not.
theorem idWeight (size: Nat) (x: Nat) (hL: digitCount x <= size): idTerms copiesWeight size x = (Nat.keepIf x (repeats x)).toInt :=
  let m := blockCount x
  let hc: m <= Succ (size - 1) :=
    Nat.leTrans m size (Succ (size - 1)) (Nat.leTrans m (digitCount x) size (blockCountLe x) hL) (Nat.predLeSucc size (size - 1) (Nat.leRefl (size - 1)))
  calc idTerms copiesWeight size x
    _ = x.toInt * divisorWeights copiesWeight m (size - 1) := idTermsDivisors copiesWeight size x hL
    _ = x.toInt * divisorWeights copiesWeight m (m - 1)    := Eq.cong (t => x.toInt * t) (divisorWeightsAll copiesWeight m (blockCountPos x) (size - 1) hc)
    _ = x.toInt * (Bool.toNat (Nat.leq 2 m)).toInt   := Eq.cong (t => x.toInt * t) (weightsOne m (blockCountPos x))
    _ = (x * Bool.toNat (Nat.leq 2 m)).toInt         := Eq.sym (Int.toIntMul x (Bool.toNat (Nat.leq 2 m)))
    _ = (Nat.keepIf x (repeats x)).toInt
        := Eq.cong Nat.toInt (Eq.trans (Nat.mulToNat x (Nat.leq 2 m)) (Eq.cong (Nat.keepIf x) (Eq.sym (repeatsBlocks x))))


-- (6) Swapping the sums ------------------------------------------------------

-- A term with more digits than `to` is 0 anyway.
theorem keptTerm (w: Nat -> Int) (r: Range) (k: Nat) (hk: 1 <= k) (n: Nat) (hn: 2 <= n):
    (if Nat.leq (k * n) (List.length (Nat.digits r.to)) then w n * (sumMatchingTemplate r { blockLength = k, copies = n }).toInt else 0) = w n * (sumMatchingTemplate r { blockLength = k, copies = n }).toInt :=
  match h: Nat.leq (k * n) (List.length (Nat.digits r.to)) with
    | True  => rfl
    | False => Eq.sym (Eq.trans (Eq.cong (t => w n * t.toInt) (repeatedZero r k hk n hn h)) (Int.mulZero (w n)))

-- The program's sum over the templates, under weights w for the copies, as a
-- grid: every block length k up to the digits of `to` and every number of
-- copies n from 2, the templates that don't fit counting 0.
def weighted (w: Nat -> Int) (r: Range): Int :=
  let size := List.length (Nat.digits r.to)
  List.rangeFrom size 1 |> .sumBy (k => List.rangeFrom (size - 1) 2 |> .sumBy (n => if Nat.leq (k * n) size then w n * (sumMatchingTemplate r { blockLength = k, copies = n }).toInt else 0))

theorem sumOfIdsWrittenRepeatedlyGrid (r: Range): sumOfIdsWrittenRepeatedly r = weighted copiesWeight r :=
  templatesSum r (template => copiesWeight template.copies * (sumMatchingTemplate r template).toInt)

-- One term of `weighted`, as a sum over the ids of the range.
theorem termIds (w: Nat -> Int) (r: Range) (k: Nat) (hk: 1 <= k) (n: Nat) (hn: 2 <= n):
    (if Nat.leq (k * n) (List.length (Nat.digits r.to)) then w n * (sumMatchingTemplate r { blockLength = k, copies = n }).toInt else 0)
      = List.sumBy (x => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) r.ids :=
  calc (if Nat.leq (k * n) (List.length (Nat.digits r.to)) then w n * (sumMatchingTemplate r { blockLength = k, copies = n }).toInt else 0)
    _ = w n * (sumMatchingTemplate r { blockLength = k, copies = n }).toInt := keptTerm w r k hk n hn
    _ = w n * (List.sumBy (x => Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids).toInt := Eq.cong (t => w n * t.toInt) (repeatedIds r k hk n hn)
    _ = w n * List.sumBy (x => (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) r.ids
        := Eq.cong (t => w n * t) (Int.toIntSumBy (x => Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids)
    _ = List.sumBy (x => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) r.ids
        := Eq.sym (Int.sumByMulLeft (w n) (x => (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) r.ids)

-- A block written n times with more digits than `to` adds nothing.
theorem repeatedZero (r: Range) (k: Nat) (hk: 1 <= k) (n: Nat) (hn: 2 <= n) (h: Nat.leq (k * n) (List.length (Nat.digits r.to)) = False): sumMatchingTemplate r { blockLength = k, copies = n } = 0 :=
  Eq.trans (repeatedIds r k hk n hn)
    (List.sumRangeNone (x => writtenAs (Nat.digits x) k n) (x => x) r.size r.from
      (x x1 x2 =>
        match t: writtenAs (Nat.digits x) k n with
          | True =>
            Void.exfalso (Nat.lessIrrefl (List.length (Nat.digits r.to))
              (calc Succ (List.length (Nat.digits r.to))
                _ <= k * n                      := Nat.leqFalse (k * n) (List.length (Nat.digits r.to)) h
                _ = List.length (Nat.digits x)  := Eq.trans (Nat.mulComm k n) (countOf x k n hn t)
                _ <= List.length (Nat.digits r.to) := idsBelow r x x1 x2))
          | False => rfl))

-- One range under weights w, id by id.
theorem weightedIds (w: Nat -> Int) (r: Range): weighted w r = List.sumBy (x => idTerms w (List.length (Nat.digits r.to)) x) r.ids :=
  let size := List.length (Nat.digits r.to)
  calc weighted w r
    _ = List.sumBy (k => List.sumBy (n => List.sumBy (x => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) r.ids) (List.rangeFrom (size - 1) 2)) (List.rangeFrom size 1)
        := List.sumRangeCongr (k => List.sumBy (n => if Nat.leq (k * n) size then w n * (sumMatchingTemplate r { blockLength = k, copies = n }).toInt else 0) (List.rangeFrom (size - 1) 2))
             (k => List.sumBy (n => List.sumBy (x => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) r.ids) (List.rangeFrom (size - 1) 2)) size 1
             (k k1 k2 => List.sumRangeCongr (n => if Nat.leq (k * n) size then w n * (sumMatchingTemplate r { blockLength = k, copies = n }).toInt else 0)
               (n => List.sumBy (x => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) r.ids) (size - 1) 2
               (n n1 n2 => termIds w r k k1 n n1))
    _ = List.sumBy (k => List.sumBy (x => List.sumBy (n => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) (List.rangeFrom (size - 1) 2)) r.ids) (List.rangeFrom size 1)
        := List.sumByCong (k => List.sumBy (n => List.sumBy (x => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) r.ids) (List.rangeFrom (size - 1) 2))
             (k => List.sumBy (x => List.sumBy (n => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) (List.rangeFrom (size - 1) 2)) r.ids)
             (List.rangeFrom size 1)
             (k => List.sumBySwap (n x => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) r.ids (List.rangeFrom (size - 1) 2))
    _ = List.sumBy (x => idTerms w size x) r.ids
        := List.sumBySwap (k x => List.sumBy (n => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) (List.rangeFrom (size - 1) 2)) r.ids (List.rangeFrom size 1)

-- One range: the signed total is the puzzle's sum, embedded.
theorem rangeWeighted (r: Range): weighted copiesWeight r = (List.sum (List.filter repeats r.ids)).toInt :=
  let size := List.length (Nat.digits r.to)
  calc weighted copiesWeight r
    _ = List.sumBy (x => idTerms copiesWeight size x) r.ids := weightedIds copiesWeight r
    _ = List.sumBy (x => (Nat.keepIf x (repeats x)).toInt) r.ids
        := List.sumRangeCongr (x => idTerms copiesWeight size x) (x => (Nat.keepIf x (repeats x)).toInt) r.size r.from
             (x x1 x2 => idWeight size x (idsBelow r x x1 x2))
    _ = (List.sumBy (x => Nat.keepIf x (repeats x)) r.ids).toInt := Eq.sym (Int.toIntSumBy (x => Nat.keepIf x (repeats x)) r.ids)
    _ = (List.sum (List.filter repeats r.ids)).toInt := Eq.cong Nat.toInt (Eq.sym (List.sumFilter repeats r.ids))


-- Part 2 is right -------------------------------------------------------------

-- The puzzle's method: in every range walk the ids, keep those whose digits
-- are some block written two or more times, add them up.
def part2Spec (ranges: List Range): Nat :=
  ranges |> .sumBy (r => r.ids |> .filter repeats |> .sum)

test "part 2 spec" := part2Spec exampleRanges == 4174379265

-- Part 2 is the sum of the ids, in all the ranges, whose digits are some
-- block written two or more times. For every input. The signed total over
-- the ranges is the natural answer, embedded; that is what makes the
-- conversion back with `Int.toNat` right.
theorem part2Correct (ranges: List Range): solvePart2 ranges = part2Spec ranges :=
  calc solvePart2 ranges
    _ = Int.toNat (List.sumBy (r => (List.sum (List.filter repeats (Range.ids r))).toInt) ranges)
        := Eq.cong Int.toNat (List.sumByCong sumOfIdsWrittenRepeatedly (r => (List.sum (List.filter repeats (Range.ids r))).toInt) ranges (r => Eq.trans (sumOfIdsWrittenRepeatedlyGrid r) (rangeWeighted r)))
    _ = Int.toNat (part2Spec ranges).toInt
        := Eq.cong Int.toNat (Eq.sym (Int.toIntSumBy (r => List.sum (List.filter repeats (Range.ids r))) ranges))
    _ = part2Spec ranges := Int.toNatToInt (part2Spec ranges)
