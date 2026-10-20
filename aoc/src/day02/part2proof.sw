-- Why part 2 is right: `part2Correct` says the printed part 2 is `part2Spec`,
-- the puzzle's own method (walk every id of every range, keep those whose
-- digits are some block written two or more times, add them up), for every
-- input whose ids have at most 10 digits (`parseRanges` refuses others).
--
-- The outline. Take one id `x` with L digits, and let `copies x n` say that
-- its digits are some block written n times (the block then has L / n
-- digits). The implementation adds x once for each n in 2, 3, 5, 7 with
-- `copies x n`, and takes it away once for each n in 6, 10. The puzzle wants x
-- once if `copies x n` for any n. These agree because of a few facts about
-- which repeat counts come together: 4 copies are also 2 copies (`1111` is
-- `11` twice), 6 copies are 2 and 3 copies, and 2 and 3 copies together are 6
-- copies (`abcabc` = `ababab` forces a = b = c), and so on. With at most 10
-- digits each fact concerns a block of at most 3 digits, so each is proved
-- by checking every such block (`viaBlocks`), and the counting itself by
-- checking every combination of the facts (`agreeAll`).
--
-- The rest moves the sums around: (1) `repeated r k n` adds the ids of the
-- range whose digits are a k-digit block written n times (`repeatedIds`, as
-- `repeatedTwice` does for n = 2); (2) the `Int` total with weights 1, 0 and
-- -1 is a sum of plus terms minus a sum of minus terms (`invalidSplit`); (3)
-- swapping the order of the sums gives, for each id, the counts above
-- (`weightedIds`, `rangeSplit`).

namespace Aoc.Day02.Proofs
import Aoc.Common (Range, rangeEnd)
import Aoc.Day02 (..)

-- (1) n copies ------------------------------------------------------------
-- The twice* lemmas of day02.sw, for any number of copies n >= 2.

-- The digits `p` written n times make `fromDigits p` written n times.
theorem fromDigitsRep (p: List Nat): (n: Nat) -> Nat.fromDigits (List.concat (List.replicate n p)) = writeTimes (List.length p) (Nat.fromDigits p) n
  | Zero   => rfl
  | Succ n =>
    calc Nat.fromDigits (List.concat (List.replicate (Succ n) p))
      _ = Nat.fromDigits (List.append (List.concat (List.replicate n p)) p) := Eq.cong Nat.fromDigits (List.concatReplicateSnoc p n)
      _ = Nat.fromDigits (List.concat (List.replicate n p)) * Nat.pow 10 (List.length p) + Nat.fromDigits p := Nat.fromDigitsAppend (List.concat (List.replicate n p)) p
      _ = writeTimes (List.length p) (Nat.fromDigits p) n * Nat.pow 10 (List.length p) + Nat.fromDigits p := Eq.cong (\t => t * Nat.pow 10 (List.length p) + Nat.fromDigits p) (fromDigitsRep p n)

theorem repAppend (x: Nat) (k: Nat) (n: Nat) (hq: writtenAs (Nat.digits x) k n = True):
    List.concat (List.replicate n (List.take k (Nat.digits x))) = Nat.digits x :=
  Decidable.toBoolSound (List.decEq (\a b => Nat.decEq a b) (List.concat (List.replicate n (List.take k (Nat.digits x)))) (Nat.digits x)) hq

-- With two or more copies the block is k digits long (it can't be all of x).
theorem repBlockLength (x: Nat) (k: Nat) (m: Nat) (hq: writtenAs (Nat.digits x) k (Succ (Succ m)) = True): List.length (List.take k (Nat.digits x)) = k :=
  Bool.inspect (Nat.leq k (List.length (Nat.digits x))) (\u => List.length (List.take k (Nat.digits x)) = k)
    (\t => List.lengthTake k (Nat.digits x) t)
    (\f => Void.exfalso (Nat.lessIrrefl (List.length (Nat.digits x))
      (calc Succ (List.length (Nat.digits x))
        _ <= List.length (Nat.digits x) + List.length (Nat.digits x) := Nat.leCongLeft (List.length (Nat.digits x) + 1) (Succ (List.length (Nat.digits x))) (List.length (Nat.digits x) + List.length (Nat.digits x)) (Nat.addOne (List.length (Nat.digits x))) (Nat.leAddCong (List.length (Nat.digits x)) 1 (List.length (Nat.digits x)) (Nat.digitsNonEmpty x))
        _ <= List.length (Nat.digits x) + (List.length (Nat.digits x) + List.length (List.concat (List.replicate m (Nat.digits x)))) := Nat.leAddCong (List.length (Nat.digits x)) (List.length (Nat.digits x)) (List.length (Nat.digits x) + List.length (List.concat (List.replicate m (Nat.digits x)))) (Nat.leAddRight (List.length (Nat.digits x)) (List.length (List.concat (List.replicate m (Nat.digits x)))))
        _ = List.length (List.concat (List.replicate (Succ (Succ m)) (Nat.digits x))) := Eq.sym (Eq.trans (List.lengthAppend (Nat.digits x) (List.append (Nat.digits x) (List.concat (List.replicate m (Nat.digits x))))) (Eq.cong (\t => List.length (Nat.digits x) + t) (List.lengthAppend (Nat.digits x) (List.concat (List.replicate m (Nat.digits x))))))
        _ = List.length (List.concat (List.replicate (Succ (Succ m)) (List.take k (Nat.digits x)))) := Eq.cong (\l => List.length (List.concat (List.replicate (Succ (Succ m)) l))) (Eq.sym (List.takeAll k (Nat.digits x) (Nat.lessLe (List.length (Nat.digits x)) k (Nat.leqFalse k (List.length (Nat.digits x)) f))))
        _ = List.length (Nat.digits x) := Eq.cong List.length (repAppend x k (Succ (Succ m)) hq))))

-- n copies of a k-digit block: n * k digits.
theorem repCount (x: Nat) (k: Nat) (m: Nat) (hq: writtenAs (Nat.digits x) k (Succ (Succ m)) = True): Succ (Succ m) * k = List.length (Nat.digits x) :=
  Eq.trans (Eq.cong (\t => Succ (Succ m) * t) (Eq.sym (repBlockLength x k m hq)))
    (Eq.trans (Eq.sym (List.lengthConcatReplicate (List.take k (Nat.digits x)) (Succ (Succ m)))) (Eq.cong List.length (repAppend x k (Succ (Succ m)) hq)))

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
  Nat.ltCongRight (Nat.fromDigits (List.take k (Nat.digits x))) (Nat.pow 10 (List.length (List.take k (Nat.digits x)))) (Nat.pow 10 k)
    (Eq.cong (\t => Nat.pow 10 t) (repBlockLength x k m hq))
    (Nat.fromDigitsBound (List.take k (Nat.digits x)) (Nat.digitsTake k (Nat.digits x) (Nat.digitsDigits x)))

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
      _ = Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n) * Nat.pow 10 (List.length (Nat.digits b)) + Nat.fromDigits (Nat.digits b)) := Eq.cong (\t => Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n) * Nat.pow 10 (List.length (Nat.digits b)) + t)) (Eq.sym (Nat.fromDigitsDigits b))
      _ = List.append (Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n))) (Nat.digits b) := Nat.digitsShift (Nat.digits b) (writeTimes (List.length (Nat.digits b)) b (Succ n)) (writeTimesPos (List.length (Nat.digits b)) b hb n) (Nat.digitsDigits b)
      _ = List.append (List.concat (List.replicate (Succ n) (Nat.digits b))) (Nat.digits b) := Eq.cong (\l => List.append l (Nat.digits b)) (digitsRep b hb n)
      _ = List.concat (List.replicate (Succ (Succ n)) (Nat.digits b)) := Eq.sym (List.concatReplicateSnoc (Nat.digits b) (Succ n))

theorem writtenRepOf (p: List Nat) (k: Nat) (hk: List.length p = k) (n: Nat): writtenAs (List.concat (List.replicate (Succ n) p)) k (Succ n) = True :=
  Decidable.toBoolOf (List.decEq (\a b => Nat.decEq a b) (List.concat (List.replicate (Succ n) (List.take k (List.concat (List.replicate (Succ n) p))))) (List.concat (List.replicate (Succ n) p)))
    (Eq.cong (\q => List.concat (List.replicate (Succ n) q)) (Eq.trans (Eq.cong (\t => List.take t (List.append p (List.concat (List.replicate n p)))) (Eq.sym hk)) (List.takeAppend p (List.concat (List.replicate n p)))))

theorem repDigits (j: Nat) (b: Nat) (h1: Nat.pow 10 j <= b) (h2: b < Nat.pow 10 (Succ j)) (n: Nat):
    writtenAs (Nat.digits (writeTimes (Succ j) b (Succ n))) (Succ j) (Succ n) = True :=
  J (\l q => writtenAs l (Succ j) (Succ n) = True) (writtenRepOf (Nat.digits b) (Succ j) (Nat.digitsLength j b h1 h2) n)
    (Eq.sym
      (Eq.trans (Eq.cong (\t => Nat.digits (writeTimes t b (Succ n))) (Eq.sym (Nat.digitsLength j b h1 h2)))
        (digitsRep b (Nat.leTrans 1 (Nat.pow 10 j) b (Nat.powSuccPos 9 j) h1) n)))

theorem repInjective (k: Nat) (b: Nat) (v: Nat) (m: Nat) (e: writeTimes k b (Succ m) = writeTimes k v (Succ m)): b = v :=
  Nat.mulSuccCancel b v (Nat.pow 10 k * multiplier k m)
    (Eq.trans (Eq.cong (\t => b * t) (Eq.sym (multiplierSucc k m)))
      (Eq.trans (Eq.sym (writeTimesMul k b (Succ m)))
        (Eq.trans e (Eq.trans (writeTimesMul k v (Succ m)) (Eq.cong (\t => v * t) (multiplierSucc k m))))))

-- For one id `x`, block length k and n copies: the blocks written n times
-- that make `x` add up to `x` when x's digits are a k-digit block written n
-- times, and to 0 otherwise (`blockCount` for any n).
theorem blockCountRep (x: Nat) (m: Nat): (k: Nat) -> 1 <= k ->
    List.sumBy (\b => Nat.keepIf x (writeTimes k b (Succ (Succ m)) == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
      = Nat.keepIf x (writtenAs (Nat.digits x) k (Succ (Succ m)))
  | Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ j, h =>
    Bool.inspect (writtenAs (Nat.digits x) (Succ j) (Succ (Succ m)))
      (\u => List.sumBy (\b => Nat.keepIf x (writeTimes (Succ j) b (Succ (Succ m)) == x)) (List.rangeFrom (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j))
        = Nat.keepIf x u)
      (\hq => List.sumRangeOne (\b => writeTimes (Succ j) b (Succ (Succ m)) == x) (\b => x) (Nat.fromDigits (List.take (Succ j) (Nat.digits x)))
        (Decidable.toBoolOf (Nat.decEq (writeTimes (Succ j) (Nat.fromDigits (List.take (Succ j) (Nat.digits x))) (Succ (Succ m))) x) (repValue x (Succ j) m hq))
        (\b hb => repInjective (Succ j) b (Nat.fromDigits (List.take (Succ j) (Nat.digits x))) (Succ m)
          (Eq.trans (Decidable.toBoolSound (Nat.decEq (writeTimes (Succ j) b (Succ (Succ m))) x) hb) (Eq.sym (repValue x (Succ j) m hq))))
        (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
        (repAbove x (Succ j) m rfl hq)
        (Nat.ltCongRight (Nat.fromDigits (List.take (Succ j) (Nat.digits x))) (Nat.pow 10 (Succ j)) (Nat.pow 10 j + (Nat.pow 10 (Succ j) - Nat.pow 10 j))
          (Eq.sym (Nat.addSubCancel (Nat.pow 10 j) (Nat.pow 10 (Succ j)) (Nat.powTenPredLe (Succ j))))
          (repBelow x (Succ j) m hq)))
      (\hq => List.sumRangeNone (\b => writeTimes (Succ j) b (Succ (Succ m)) == x) (\b => x) (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
        (\b h1 h2 => Decidable.toBoolOfNot (Nat.decEq (writeTimes (Succ j) b (Succ (Succ m))) x)
          (\e => Bool.trueNotFalse (Eq.trans
            (Eq.sym (J (\y q => writtenAs (Nat.digits y) (Succ j) (Succ (Succ m)) = True)
              (repDigits j b h1
                (Nat.ltCongRight b (Nat.pow 10 j + (Nat.pow 10 (Succ j) - Nat.pow 10 j)) (Nat.pow 10 (Succ j))
                  (Nat.addSubCancel (Nat.pow 10 j) (Nat.pow 10 (Succ j)) (Nat.powTenPredLe (Succ j))) h2)
                (Succ m))
              e))
            hq))))

-- One block length, as a sum over the ids of the range (`blocksAsIds` for any n).
theorem blocksAsIdsRep (r: Range) (k: Nat) (n: Nat):
    repeatedSpec r k n
      = List.sumBy (\x => List.sumBy (\b => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
          (List.rangeFrom (r.hi + 1 - r.lo) r.lo) :=
  Eq.trans (List.sumFilter (\x => r.lo <= x && x <= r.hi) (List.map (\b => writeTimes k b n) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))))
    (Eq.trans (List.sumByMap (\y => Nat.keepIf y (r.lo <= y && y <= r.hi)) (\b => writeTimes k b n) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
      (Eq.trans
        (List.sumByCongr (\b => Nat.keepIf (writeTimes k b n) (r.lo <= writeTimes k b n && writeTimes k b n <= r.hi))
          (\b => List.sumBy (\x => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (r.hi + 1 - r.lo) r.lo))
          (\b => Eq.sym (sumIdsEq r.lo r.hi (writeTimes k b n)))
          (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
        (List.sumBySwap (\b x => Nat.keepIf x (writeTimes k b n == x)) (List.rangeFrom (r.hi + 1 - r.lo) r.lo) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))))

-- (1) `repeated r k n` adds the ids of the range whose digits are a k-digit
-- block written n times.
theorem repeatedIds (r: Range) (k: Nat) (hk: 1 <= k): (n: Nat) -> 2 <= n ->
    repeated r k n = List.sumBy (\x => Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids
  | Zero,          h => Void.exfalso (Bool.falseNotTrue h)
  | Succ Zero,     h => Void.exfalso (Bool.falseNotTrue h)
  | Succ (Succ m), h =>
    Eq.trans (repeatedCorrect r k (Succ (Succ m)))
      (Eq.trans (blocksAsIdsRep r k (Succ (Succ m)))
        (List.sumByCongr (\x => List.sumBy (\b => Nat.keepIf x (writeTimes k b (Succ (Succ m)) == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
          (\x => Nat.keepIf x (writtenAs (Nat.digits x) k (Succ (Succ m)))) (\x => blockCountRep x m k hk) r.ids))

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

theorem copiesAtMost (x: Nat) (k: Nat) (n: Nat) (hn: 2 <= n) (hk: 1 <= k) (hq: writtenAs (Nat.digits x) k n = True): n <= List.length (Nat.digits x) :=
  Nat.leCongRight n (n * k) (List.length (Nat.digits x)) (countOf x k n hn hq) (Nat.leMulPos n k hk)


-- (3a) The facts about repeat counts -------------------------------------

-- The digits of `x` are some block written n times.
def copies (x: Nat) (n: Nat): Bool :=
  List.rangeFrom (Nat.digits x).length 1 |> .any (\k => writtenAs (Nat.digits x) k n)

-- n divides L.
def divides (n: Nat) (l: Nat): Bool := List.rangeFrom l 1 |> .any (\k => n * k == l)

theorem copiesDivide (x: Nat) (n: Nat) (hn: 2 <= n) (h: copies x n = True): divides n (List.length (Nat.digits x)) = True :=
  List.anyRangeElim (\k => writtenAs (Nat.digits x) k n) (divides n (List.length (Nat.digits x)) = True) (List.length (Nat.digits x)) 1 h
    (\k h1 h2 hk => List.anyRangeIntro (\k => n * k == List.length (Nat.digits x)) (List.length (Nat.digits x)) 1 k h1 h2
      (Decidable.toBoolOf (Nat.decEq (n * k) (List.length (Nat.digits x))) (countOf x k n hn hk)))

-- The k-digit blocks, from 10^(k-1) to 10^k - 1.
def blocks (k: Nat): List Nat := List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))

-- `q` holds for every block written n times that has at most 10 digits.
def blockCheck (n: Nat) (q: Nat -> Bool) (top: Nat): Bool :=
  List.rangeFrom top 1 |> .all (\k => Bool.ifThenElse (Nat.leq (n * k) top) (\u => List.all (\b => q (writeTimes k b n)) (blocks k)) (\u => True))

-- So it holds for every id of at most 10 digits whose digits are a block
-- written n times.
theorem blockStep (n: Nat) (q: Nat -> Bool) (k: Nat) (top: Nat) (hk: n * k <= top)
    (inner: Bool.ifThenElse (Nat.leq (n * k) top) (\u => List.all (\b => q (writeTimes k b n)) (blocks k)) (\u => True) = True):
    List.all (\b => q (writeTimes k b n)) (blocks k) = True :=
  Eq.trans (Eq.cong (\c => Bool.ifThenElse c (\u => List.all (\b => q (writeTimes k b n)) (blocks k)) (\u => True)) (Eq.sym hk)) inner

theorem viaBlocks (n: Nat) (hn: 2 <= n) (q: Nat -> Bool) (top: Nat)
    (check: (t: Nat) -> t = top -> blockCheck n q t = True) (x: Nat) (hL: List.length (Nat.digits x) <= top) (h: copies x n = True): q x = True :=
  List.anyRangeElim (\k => writtenAs (Nat.digits x) k n) (q x = True) (List.length (Nat.digits x)) 1 h
    (\k h1 h2 hk => J (\y e => q y = True)
      (List.allRangeElim (\b => q (writeTimes k b n)) (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))
        (blockStep n q k top (Nat.leCongLeft (List.length (Nat.digits x)) (n * k) top (Eq.sym (countOf x k n hn hk)) hL)
          (List.allRangeElim (\k => Bool.ifThenElse (Nat.leq (n * k) top) (\u => List.all (\b => q (writeTimes k b n)) (blocks k)) (\u => True)) top 1 (check top rfl) k h1
            (Nat.leTrans k (List.length (Nat.digits x)) top (blockAtMost x k n hn hk) hL)))
        (Nat.fromDigits (List.take k (Nat.digits x)))
        (aboveOf x k h1 n hn hk)
        (Nat.ltCongRight (Nat.fromDigits (List.take k (Nat.digits x))) (Nat.pow 10 k) (Nat.pow 10 (k - 1) + (Nat.pow 10 k - Nat.pow 10 (k - 1)))
          (Eq.sym (Nat.addSubCancel (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (Nat.powTenPredLe k)))
          (belowOf x k n hn hk)))
      (valueOf x k n hn hk))

-- The facts, each checked on every block that fits.
theorem fourChecked: (t: Nat) -> t = 10 -> blockCheck 4 (\y => copies y 2) t = True := \t e => J (\s p => blockCheck 4 (\y => copies y 2) s = True) rfl (Eq.sym e)
theorem eightChecked: (t: Nat) -> t = 10 -> blockCheck 8 (\y => copies y 2) t = True := \t e => J (\s p => blockCheck 8 (\y => copies y 2) s = True) rfl (Eq.sym e)
theorem nineChecked: (t: Nat) -> t = 10 -> blockCheck 9 (\y => copies y 3) t = True := \t e => J (\s p => blockCheck 9 (\y => copies y 3) s = True) rfl (Eq.sym e)
theorem sixChecked: (t: Nat) -> t = 10 -> blockCheck 6 (\y => copies y 2 && copies y 3) t = True := \t e => J (\s p => blockCheck 6 (\y => copies y 2 && copies y 3) s = True) rfl (Eq.sym e)
theorem tenChecked: (t: Nat) -> t = 10 -> blockCheck 10 (\y => copies y 2 && copies y 5) t = True := \t e => J (\s p => blockCheck 10 (\y => copies y 2 && copies y 5) s = True) rfl (Eq.sym e)
theorem threeChecked: (t: Nat) -> t = 10 -> blockCheck 3 (\y => Bool.not (copies y 2) || copies y 6) t = True := \t e => J (\s p => blockCheck 3 (\y => Bool.not (copies y 2) || copies y 6) s = True) rfl (Eq.sym e)
theorem fiveChecked: (t: Nat) -> t = 10 -> blockCheck 5 (\y => Bool.not (copies y 2) || copies y 10) t = True := \t e => J (\s p => blockCheck 5 (\y => Bool.not (copies y 2) || copies y 10) s = True) rfl (Eq.sym e)

-- All the facts at once, for an id of at most 10 digits.
def validFor (l: Nat) (c: Nat -> Bool): Bool :=
  List.all (\n => Bool.not (c n) || divides n l) (List.rangeFrom 9 2)
    && ((Bool.not (c 4) || c 2)
    && ((Bool.not (c 8) || c 2)
    && ((Bool.not (c 9) || c 3)
    && ((Bool.not (c 6) || (c 2 && c 3))
    && ((Bool.not (c 10) || (c 2 && c 5))
    && ((Bool.not (c 3) || (Bool.not (c 2) || c 6))
    && (Bool.not (c 5) || (Bool.not (c 2) || c 10))))))))

theorem validCopies (x: Nat) (hL: List.length (Nat.digits x) <= 10): validFor (List.length (Nat.digits x)) (copies x) = True :=
  Bool.andIntro _ _
    (List.allRangeIntro (\n => Bool.not (copies x n) || divides n (List.length (Nat.digits x))) 9 2
      (\n h1 h2 => Bool.impIntro (copies x n) (divides n (List.length (Nat.digits x))) (copiesDivide x n h1)))
    (Bool.andIntro _ _ (Bool.impIntro (copies x 4) (copies x 2) (viaBlocks 4 rfl (\y => copies y 2) 10 fourChecked x hL))
    (Bool.andIntro _ _ (Bool.impIntro (copies x 8) (copies x 2) (viaBlocks 8 rfl (\y => copies y 2) 10 eightChecked x hL))
    (Bool.andIntro _ _ (Bool.impIntro (copies x 9) (copies x 3) (viaBlocks 9 rfl (\y => copies y 3) 10 nineChecked x hL))
    (Bool.andIntro _ _ (Bool.impIntro (copies x 6) (copies x 2 && copies x 3) (viaBlocks 6 rfl (\y => copies y 2 && copies y 3) 10 sixChecked x hL))
    (Bool.andIntro _ _ (Bool.impIntro (copies x 10) (copies x 2 && copies x 5) (viaBlocks 10 rfl (\y => copies y 2 && copies y 5) 10 tenChecked x hL))
    (Bool.andIntro _ _ (Bool.impIntro (copies x 3) (Bool.not (copies x 2) || copies x 6) (viaBlocks 3 rfl (\y => Bool.not (copies y 2) || copies y 6) 10 threeChecked x hL))
      (Bool.impIntro (copies x 5) (Bool.not (copies x 2) || copies x 10) (viaBlocks 5 rfl (\y => Bool.not (copies y 2) || copies y 10) 10 fiveChecked x hL))))))))


-- (3b) Counting ------------------------------------------------------------

-- The repeat counts with weight 1, and with weight -1.
def plus: Nat -> Bool
  | 2 => True
  | 3 => True
  | 5 => True
  | 7 => True
  | _ => False

def minus: Nat -> Bool
  | 6  => True
  | 10 => True
  | _  => False

-- How many of the repeat counts 2 to 10 that `u` picks hold.
def count (u: Nat -> Bool) (c: Nat -> Bool): Nat := List.rangeFrom 9 2 |> .sumBy (\n => Bool.toNat (c n && u n))

def anyCopies (c: Nat -> Bool): Bool := List.rangeFrom 9 2 |> .any c

-- With the facts, the plus counts are the minus counts and one more if any hold.
def agree (l: Nat) (c: Nat -> Bool): Bool :=
  Bool.not (validFor l c) || (count plus c == Bool.toNat (anyCopies c) + count minus c)

-- Checking `agree` for every number of digits and every combination.
def pick (v2: Bool) (v3: Bool) (v4: Bool) (v5: Bool) (v6: Bool) (v7: Bool) (v8: Bool) (v9: Bool) (v10: Bool): Nat -> Bool
  | 2  => v2
  | 3  => v3
  | 4  => v4
  | 5  => v5
  | 6  => v6
  | 7  => v7
  | 8  => v8
  | 9  => v9
  | 10 => v10
  | _  => False

def allBool (f: Bool -> Bool): Bool := f True && f False

theorem allBoolElim (f: Bool -> Bool) (h: allBool f = True): (b: Bool) -> f b = True
  | True  => Bool.andLeft (f True) (f False) h
  | False => Bool.andRight (f True) (f False) h

def check10 (l: Nat) (v2: Bool) (v3: Bool) (v4: Bool) (v5: Bool) (v6: Bool) (v7: Bool) (v8: Bool) (v9: Bool): Bool := allBool (\v10 => agree l (pick v2 v3 v4 v5 v6 v7 v8 v9 v10))
def check9 (l: Nat) (v2: Bool) (v3: Bool) (v4: Bool) (v5: Bool) (v6: Bool) (v7: Bool) (v8: Bool): Bool := allBool (\v9 => check10 l v2 v3 v4 v5 v6 v7 v8 v9)
def check8 (l: Nat) (v2: Bool) (v3: Bool) (v4: Bool) (v5: Bool) (v6: Bool) (v7: Bool): Bool := allBool (\v8 => check9 l v2 v3 v4 v5 v6 v7 v8)
def check7 (l: Nat) (v2: Bool) (v3: Bool) (v4: Bool) (v5: Bool) (v6: Bool): Bool := allBool (\v7 => check8 l v2 v3 v4 v5 v6 v7)
def check6 (l: Nat) (v2: Bool) (v3: Bool) (v4: Bool) (v5: Bool): Bool := allBool (\v6 => check7 l v2 v3 v4 v5 v6)
def check5 (l: Nat) (v2: Bool) (v3: Bool) (v4: Bool): Bool := allBool (\v5 => check6 l v2 v3 v4 v5)
def check4 (l: Nat) (v2: Bool) (v3: Bool): Bool := allBool (\v4 => check5 l v2 v3 v4)
def check3 (l: Nat) (v2: Bool): Bool := allBool (\v3 => check4 l v2 v3)
def check2 (l: Nat): Bool := allBool (\v2 => check3 l v2)

theorem allChecked: List.all check2 (List.rangeFrom 10 1) = True := rfl

theorem agreeAll (l: Nat) (h1: 1 <= l) (h2: l <= 10) (c: Nat -> Bool): agree l (pick (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) (c 9) (c 10)) = True :=
  allBoolElim (\v10 => agree l (pick (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) (c 9) v10))
    (allBoolElim (\v9 => check10 l (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) v9)
      (allBoolElim (\v8 => check9 l (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) v8)
        (allBoolElim (\v7 => check8 l (c 2) (c 3) (c 4) (c 5) (c 6) v7)
          (allBoolElim (\v6 => check7 l (c 2) (c 3) (c 4) (c 5) v6)
            (allBoolElim (\v5 => check6 l (c 2) (c 3) (c 4) v5)
              (allBoolElim (\v4 => check5 l (c 2) (c 3) v4)
                (allBoolElim (\v3 => check4 l (c 2) v3)
                  (allBoolElim (\v2 => check3 l v2) (List.allRangeElim check2 10 1 allChecked l h1 h2) (c 2))
                  (c 3))
                (c 4))
              (c 5))
            (c 6))
          (c 7))
        (c 8))
      (c 9))
    (c 10)

-- For one id of at most 10 digits.
theorem countsFor (x: Nat) (hL: List.length (Nat.digits x) <= 10):
    count plus (copies x) = Bool.toNat (anyCopies (copies x)) + count minus (copies x) :=
  Decidable.toBoolSound (Nat.decEq (count plus (copies x)) (Bool.toNat (anyCopies (copies x)) + count minus (copies x)))
    (Bool.impElim (validFor (List.length (Nat.digits x)) (copies x)) (count plus (copies x) == Bool.toNat (anyCopies (copies x)) + count minus (copies x))
      (agreeAll (List.length (Nat.digits x)) (Nat.digitsNonEmpty x) hL (copies x))
      (validCopies x hL))

-- The puzzle's test, `repeats`, is "some repeat count from 2 to 10 holds".
theorem repeatsCopies (x: Nat) (hL: List.length (Nat.digits x) <= 10): repeats x = anyCopies (copies x) :=
  Bool.eqOf (repeats x) (anyCopies (copies x))
    (\h => List.anyRangeElim (\k => List.any (\n => writtenAs (Nat.digits x) k n) (List.rangeFrom (List.length (Nat.digits x)) 2)) (anyCopies (copies x) = True) (List.length (Nat.digits x)) 1 h
      (\k h1 h2 hk => List.anyRangeElim (\n => writtenAs (Nat.digits x) k n) (anyCopies (copies x) = True) (List.length (Nat.digits x)) 2 hk
        (\n n1 n2 hw => List.anyRangeIntro (copies x) 9 2 n n1 (Nat.leTrans n (List.length (Nat.digits x)) 10 (copiesAtMost x k n n1 h1 hw) hL)
          (List.anyRangeIntro (\k => writtenAs (Nat.digits x) k n) (List.length (Nat.digits x)) 1 k h1 h2 hw))))
    (\h => List.anyRangeElim (copies x) (repeats x = True) 9 2 h
      (\n n1 n2 hc => List.anyRangeElim (\k => writtenAs (Nat.digits x) k n) (repeats x = True) (List.length (Nat.digits x)) 1 hc
        (\k h1 h2 hw => List.anyRangeIntro (\k => List.any (\n => writtenAs (Nat.digits x) k n) (List.rangeFrom (List.length (Nat.digits x)) 2)) (List.length (Nat.digits x)) 1 k h1 h2
          (List.anyRangeIntro (\n => writtenAs (Nat.digits x) k n) (List.length (Nat.digits x)) 2 n n1
            (Nat.leTrans (Succ n) (Succ (List.length (Nat.digits x))) (Succ (Succ (List.length (Nat.digits x)))) (copiesAtMost x k n n1 h1 hw) (Nat.leSucc (Succ (List.length (Nat.digits x)))))
            hw))))

-- One id: x times the plus count is x if it repeats, plus x times the minus count.
theorem perId (x: Nat) (hL: List.length (Nat.digits x) <= 10):
    x * count plus (copies x) = Nat.keepIf x (repeats x) + x * count minus (copies x) :=
  calc x * count plus (copies x)
    _ = x * (Bool.toNat (anyCopies (copies x)) + count minus (copies x)) := Eq.cong (\t => x * t) (countsFor x hL)
    _ = x * Bool.toNat (anyCopies (copies x)) + x * count minus (copies x) := Nat.mulDistribLeft x (Bool.toNat (anyCopies (copies x))) (count minus (copies x))
    _ = Nat.keepIf x (anyCopies (copies x)) + x * count minus (copies x) := Eq.cong (\t => t + x * count minus (copies x)) (Nat.mulToNat x (anyCopies (copies x)))
    _ = Nat.keepIf x (repeats x) + x * count minus (copies x) := Eq.cong (\t => Nat.keepIf x t + x * count minus (copies x)) (Eq.sym (repeatsCopies x hL))


-- (3c) Swapping the sums ---------------------------------------------------

-- For one id and repeat count, over all block lengths up to `size`: x if
-- some block written n times makes x, else 0.
theorem collapse (x: Nat) (n: Nat) (hn: 2 <= n) (size: Nat) (hLS: List.length (Nat.digits x) <= size):
    List.sumBy (\k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1) = Nat.keepIf x (copies x n) :=
  Bool.inspect (copies x n) (\u => List.sumBy (\k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1) = Nat.keepIf x u)
    (\hc => List.anyRangeElim (\k => writtenAs (Nat.digits x) k n) (List.sumBy (\k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom size 1) = x) (List.length (Nat.digits x)) 1 hc
      (\k0 h1 h2 hk0 => List.sumRangeOne (\k => writtenAs (Nat.digits x) k n) (\k => x) k0 hk0
        (\k hk => Nat.mulCancelLeft n (Nat.leTrans 1 2 n rfl hn) k k0 (Eq.trans (countOf x k n hn hk) (Eq.sym (countOf x k0 n hn hk0))))
        size 1 h1 (Nat.leTrans (Succ k0) (Succ (List.length (Nat.digits x))) (Succ size) h2 hLS)))
    (\hc => List.sumRangeNone (\k => writtenAs (Nat.digits x) k n) (\k => x) size 1
      (\k h1 h2 => Bool.inspect (writtenAs (Nat.digits x) k n) (\u => u = False)
        (\t => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (List.anyRangeIntro (\k => writtenAs (Nat.digits x) k n) (List.length (Nat.digits x)) 1 k h1 (blockAtMost x k n hn t) t)) hc)))
        (\f => rfl)))

-- The ids of a range have at most as many digits as its end.
theorem idsBelow (r: Range) (x: Nat) (h1: r.lo <= x) (h2: x < r.lo + r.size): List.length (Nat.digits x) <= List.length (Nat.digits r.hi) :=
  Nat.digitsLengthLe x (List.length (Nat.digits r.hi)) (Nat.digitsNonEmpty r.hi)
    (Nat.leTrans (Succ x) (Succ r.hi) (Nat.pow 10 (List.length (Nat.digits r.hi))) (rangeEnd r.lo r.hi x h1 h2) (Nat.ltPowTenDigits r.hi))

-- The terms of `invalid` whose weight `u` picks, added up.
def weighted (u: Nat -> Bool) (r: Range): Nat :=
  List.rangeFrom (Nat.digits r.hi).length 1 |> .sumBy (\k => List.rangeFrom 9 2 |> .sumBy (\n => Nat.keepIf (repeated r k n) (u n)))

theorem weightedIds (u: Nat -> Bool) (r: Range): weighted u r = List.sumBy (\x => x * count u (copies x)) r.ids :=
  calc weighted u r
    _ = List.sumBy (\k => List.sumBy (\n => List.sumBy (\x => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) r.ids) (List.rangeFrom 9 2)) (List.rangeFrom (List.length (Nat.digits r.hi)) 1) :=
      List.sumRangeCongr (\k => List.sumBy (\n => Nat.keepIf (repeated r k n) (u n)) (List.rangeFrom 9 2))
        (\k => List.sumBy (\n => List.sumBy (\x => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) r.ids) (List.rangeFrom 9 2))
        (List.length (Nat.digits r.hi)) 1
        (\k k1 k2 => List.sumRangeCongr (\n => Nat.keepIf (repeated r k n) (u n)) (\n => List.sumBy (\x => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) r.ids) 9 2
          (\n n1 n2 => Eq.trans (Eq.cong (\t => Nat.keepIf t (u n)) (repeatedIds r k k1 n n1)) (Nat.keepIfSumBy (\x => Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids (u n))))
    _ = List.sumBy (\k => List.sumBy (\x => List.sumBy (\n => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) (List.rangeFrom 9 2)) r.ids) (List.rangeFrom (List.length (Nat.digits r.hi)) 1) :=
      List.sumByCongr (\k => List.sumBy (\n => List.sumBy (\x => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) r.ids) (List.rangeFrom 9 2))
        (\k => List.sumBy (\x => List.sumBy (\n => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) (List.rangeFrom 9 2)) r.ids)
        (\k => List.sumBySwap (\n x => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) r.ids (List.rangeFrom 9 2))
        (List.rangeFrom (List.length (Nat.digits r.hi)) 1)
    _ = List.sumBy (\x => List.sumBy (\k => List.sumBy (\n => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) (List.rangeFrom 9 2)) (List.rangeFrom (List.length (Nat.digits r.hi)) 1)) r.ids :=
      List.sumBySwap (\k x => List.sumBy (\n => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) (List.rangeFrom 9 2)) r.ids (List.rangeFrom (List.length (Nat.digits r.hi)) 1)
    _ = List.sumBy (\x => List.sumBy (\n => List.sumBy (\k => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) (List.rangeFrom (List.length (Nat.digits r.hi)) 1)) (List.rangeFrom 9 2)) r.ids :=
      List.sumByCongr (\x => List.sumBy (\k => List.sumBy (\n => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) (List.rangeFrom 9 2)) (List.rangeFrom (List.length (Nat.digits r.hi)) 1))
        (\x => List.sumBy (\n => List.sumBy (\k => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) (List.rangeFrom (List.length (Nat.digits r.hi)) 1)) (List.rangeFrom 9 2))
        (\x => List.sumBySwap (\k n => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) (List.rangeFrom 9 2) (List.rangeFrom (List.length (Nat.digits r.hi)) 1))
        r.ids
    _ = List.sumBy (\x => List.sumBy (\n => Nat.keepIf (Nat.keepIf x (copies x n)) (u n)) (List.rangeFrom 9 2)) r.ids :=
      List.sumRangeCongr (\x => List.sumBy (\n => List.sumBy (\k => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) (List.rangeFrom (List.length (Nat.digits r.hi)) 1)) (List.rangeFrom 9 2))
        (\x => List.sumBy (\n => Nat.keepIf (Nat.keepIf x (copies x n)) (u n)) (List.rangeFrom 9 2))
        r.size r.lo
        (\x x1 x2 => List.sumRangeCongr (\n => List.sumBy (\k => Nat.keepIf (Nat.keepIf x (writtenAs (Nat.digits x) k n)) (u n)) (List.rangeFrom (List.length (Nat.digits r.hi)) 1))
          (\n => Nat.keepIf (Nat.keepIf x (copies x n)) (u n)) 9 2
          (\n n1 n2 => Eq.trans (Eq.sym (Nat.keepIfSumBy (\k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) (List.rangeFrom (List.length (Nat.digits r.hi)) 1) (u n)))
            (Eq.cong (\t => Nat.keepIf t (u n)) (collapse x n n1 (List.length (Nat.digits r.hi)) (idsBelow r x x1 x2)))))
    _ = List.sumBy (\x => x * count u (copies x)) r.ids :=
      List.sumByCongr (\x => List.sumBy (\n => Nat.keepIf (Nat.keepIf x (copies x n)) (u n)) (List.rangeFrom 9 2)) (\x => x * count u (copies x))
        (\x => Eq.trans (List.sumByCongr (\n => Nat.keepIf (Nat.keepIf x (copies x n)) (u n)) (\n => x * Bool.toNat (copies x n && u n)) (\n => Nat.keepIfKeepIf x (copies x n) (u n)) (List.rangeFrom 9 2))
          (List.sumByMulLeft x (\n => Bool.toNat (copies x n && u n)) (List.rangeFrom 9 2)))
        r.ids

theorem fitsBelow (r: Range) (h: fits r = True): r.hi < 10000000000 := Eq.trans (Eq.sym (Bool.decTrueToBool (Nat.leq (Succ r.hi) 10000000000))) h

-- (3) One range: the plus terms are the puzzle's sum plus the minus terms.
theorem rangeSplit (r: Range) (small: fits r = True): weighted plus r = List.sum (List.filter repeats r.ids) + weighted minus r :=
  calc weighted plus r
    _ = List.sumBy (\x => x * count plus (copies x)) r.ids := weightedIds plus r
    _ = List.sumBy (\x => Nat.keepIf x (repeats x) + x * count minus (copies x)) r.ids :=
      List.sumRangeCongr (\x => x * count plus (copies x)) (\x => Nat.keepIf x (repeats x) + x * count minus (copies x)) r.size r.lo
        (\x x1 x2 => perId x (Nat.digitsLengthLe x 10 rfl (Nat.leTrans (Succ x) (Succ r.hi) 10000000000 (rangeEnd r.lo r.hi x x1 x2) (fitsBelow r small))))
    _ = List.sumBy (\x => Nat.keepIf x (repeats x)) r.ids + List.sumBy (\x => x * count minus (copies x)) r.ids :=
      List.sumByAdd (\x => Nat.keepIf x (repeats x)) (\x => x * count minus (copies x)) r.ids
    _ = List.sum (List.filter repeats r.ids) + weighted minus r :=
      Eq.trans (Eq.cong (\t => t + List.sumBy (\x => x * count minus (copies x)) r.ids) (Eq.sym (List.sumFilter repeats r.ids)))
        (Eq.cong (\t => List.sum (List.filter repeats r.ids) + t) (Eq.sym (weightedIds minus r)))


-- (2) The Int total ----------------------------------------------------------
-- A running total `p - q`: each term with weight 1 adds to `p`, each with
-- weight -1 to `q`.

theorem zeroCase (p: Nat) (q: Nat) (r: Nat): Int.add (Int.subNatNat p q) (Int.mul (OfNat 0) (Nat.toInt r)) = Int.subNatNat p q :=
  Int.addZero (Int.subNatNat p q)

theorem plusCase (p: Nat) (q: Nat) (r: Nat): Int.add (Int.subNatNat p q) (Int.mul (OfNat 1) (Nat.toInt r)) = Int.subNatNat (r + p) q :=
  Eq.trans (Eq.cong (\t => Int.add (Int.subNatNat p q) (OfNat t)) (Nat.addZero r))
    (Eq.trans (Int.subNatNatAddOfNat r p q) (Eq.cong (\t => Int.subNatNat t q) (Nat.addComm p r)))

theorem minusCase (p: Nat) (q: Nat) (r: Nat): Int.add (Int.subNatNat p q) (Int.mul (NegSucc 0) (Nat.toInt r)) = Int.subNatNat p (r + q) :=
  Eq.trans (Eq.cong (\t => Int.add (Int.subNatNat p q) (Int.neg (OfNat t))) (Nat.addZero r))
    (Eq.trans (Int.subNatNatAddNeg p q r) (Eq.cong (Int.subNatNat p) (Nat.addComm q r)))

theorem weightStep: (n: Nat) -> (p: Nat) -> (q: Nat) -> (r: Nat) ->
    Int.add (Int.subNatNat p q) (weight n * Nat.toInt r) = Int.subNatNat (Nat.keepIf r (plus n) + p) (Nat.keepIf r (minus n) + q)
  | 0,  p, q, r => zeroCase p q r
  | 1,  p, q, r => zeroCase p q r
  | 2,  p, q, r => plusCase p q r
  | 3,  p, q, r => plusCase p q r
  | 4,  p, q, r => zeroCase p q r
  | 5,  p, q, r => plusCase p q r
  | 6,  p, q, r => minusCase p q r
  | 7,  p, q, r => plusCase p q r
  | 8,  p, q, r => zeroCase p q r
  | 9,  p, q, r => zeroCase p q r
  | 10, p, q, r => minusCase p q r
  | Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ m)))))))))), p, q, r => zeroCase p q r

theorem consAcc (f: a -> Nat) (x: a) (xs: List a) (p: Nat): List.sumBy f (Cons x xs) + p = List.sumBy f xs + (f x + p) :=
  Eq.trans (Eq.cong (\t => t + p) (List.sumByCons f x xs)) (Nat.addRotate (f x) (List.sumBy f xs) p)

theorem subCong (a: Nat) (b: Nat) (c: Nat) (d: Nat) (e1: a = b) (e2: c = d): Int.subNatNat a c = Int.subNatNat b d :=
  Eq.trans (Eq.cong (\t => Int.subNatNat t c) e1) (Eq.cong (Int.subNatNat b) e2)

theorem consSub (f: a -> Nat) (g: a -> Nat) (x: a) (xs: List a) (p: Nat) (q: Nat):
    Int.subNatNat (List.sumBy f (Cons x xs) + p) (List.sumBy g (Cons x xs) + q) = Int.subNatNat (List.sumBy f xs + (f x + p)) (List.sumBy g xs + (g x + q)) :=
  subCong (List.sumBy f (Cons x xs) + p) (List.sumBy f xs + (f x + p)) (List.sumBy g (Cons x xs) + q) (List.sumBy g xs + (g x + q)) (consAcc f x xs p) (consAcc g x xs q)

theorem dropZero (x: Nat) (b: Bool) (p: Nat) (hz: x = 0): Nat.keepIf x b + p = p :=
  Eq.trans (Eq.cong (\t => Nat.keepIf t b + p) hz) (Eq.cong (\t => t + p) (Nat.keepIfZero b))

-- One block length's terms.
theorem termsFold (r: Range) (k: Nat) (size: Nat) (zero: (n: Nat) -> 2 <= n -> Nat.leq (k * n) size = False -> repeated r k n = 0):
    (c: Nat) -> (s: Nat) -> 2 <= s -> (p: Nat) -> (q: Nat) ->
    List.foldLeft Int.add (Int.subNatNat p q) (List.map (\n => weight n * (repeated r k n).toInt) (List.filter (\n => k * n <= size) (List.rangeFrom c s)))
      = Int.subNatNat (List.sumBy (\n => Nat.keepIf (repeated r k n) (plus n)) (List.rangeFrom c s) + p) (List.sumBy (\n => Nat.keepIf (repeated r k n) (minus n)) (List.rangeFrom c s) + q)
  | Zero,   s, hs, p, q => rfl
  | Succ c, s, hs, p, q =>
    Bool.inspect (k * s <= size)
      (\u => List.foldLeft Int.add (Int.subNatNat p q) (List.map (\n => weight n * (repeated r k n).toInt) (List.filter (\n => k * n <= size) (List.rangeFrom (Succ c) s)))
        = Int.subNatNat (List.sumBy (\n => Nat.keepIf (repeated r k n) (plus n)) (List.rangeFrom (Succ c) s) + p) (List.sumBy (\n => Nat.keepIf (repeated r k n) (minus n)) (List.rangeFrom (Succ c) s) + q))
      (\h => Eq.trans (Eq.cong (\xs => List.foldLeft Int.add (Int.subNatNat p q) (List.map (\n => weight n * (repeated r k n).toInt) xs)) (List.filterKeep (\n => k * n <= size) s (List.rangeFrom c (Succ s)) h))
        (Eq.trans (Eq.cong (\a => List.foldLeft Int.add a (List.map (\n => weight n * (repeated r k n).toInt) (List.filter (\n => k * n <= size) (List.rangeFrom c (Succ s))))) (weightStep s p q (repeated r k s)))
          (Eq.trans (termsFold r k size zero c (Succ s) (Nat.leTrans 2 s (Succ s) hs (Nat.leSucc s)) (Nat.keepIf (repeated r k s) (plus s) + p) (Nat.keepIf (repeated r k s) (minus s) + q))
            (Eq.sym (consSub (\n => Nat.keepIf (repeated r k n) (plus n)) (\n => Nat.keepIf (repeated r k n) (minus n)) s (List.rangeFrom c (Succ s)) p q)))))
      (\h => Eq.trans (Eq.cong (\xs => List.foldLeft Int.add (Int.subNatNat p q) (List.map (\n => weight n * (repeated r k n).toInt) xs)) (List.filterSkip (\n => k * n <= size) s (List.rangeFrom c (Succ s)) h))
        (Eq.trans (termsFold r k size zero c (Succ s) (Nat.leTrans 2 s (Succ s) hs (Nat.leSucc s)) p q)
          (Eq.sym (subCong _ _ _ _
            (Eq.trans (consAcc (\n => Nat.keepIf (repeated r k n) (plus n)) s (List.rangeFrom c (Succ s)) p)
              (Eq.cong (\t => List.sumBy (\n => Nat.keepIf (repeated r k n) (plus n)) (List.rangeFrom c (Succ s)) + t)
                (dropZero (repeated r k s) (plus s) p (zero s hs (Eq.trans (Eq.sym (Bool.decTrueToBool (Nat.leq (k * s) size))) h)))))
            (Eq.trans (consAcc (\n => Nat.keepIf (repeated r k n) (minus n)) s (List.rangeFrom c (Succ s)) q)
              (Eq.cong (\t => List.sumBy (\n => Nat.keepIf (repeated r k n) (minus n)) (List.rangeFrom c (Succ s)) + t)
                (dropZero (repeated r k s) (minus s) q (zero s hs (Eq.trans (Eq.sym (Bool.decTrueToBool (Nat.leq (k * s) size))) h)))))))))

-- All block lengths.
theorem kFold (r: Range) (size: Nat) (zero: (k: Nat) -> 1 <= k -> (n: Nat) -> 2 <= n -> Nat.leq (k * n) size = False -> repeated r k n = 0):
    (c: Nat) -> (s: Nat) -> 1 <= s -> (p: Nat) -> (q: Nat) ->
    List.foldLeft Int.add (Int.subNatNat p q) (List.concatMap (invalid.terms weight r size) (List.rangeFrom c s))
      = Int.subNatNat (List.sumBy (\k => List.sumBy (\n => Nat.keepIf (repeated r k n) (plus n)) (List.rangeFrom 9 2)) (List.rangeFrom c s) + p)
          (List.sumBy (\k => List.sumBy (\n => Nat.keepIf (repeated r k n) (minus n)) (List.rangeFrom 9 2)) (List.rangeFrom c s) + q)
  | Zero,   s, hs, p, q => rfl
  | Succ c, s, hs, p, q =>
    Eq.trans (List.foldLeftAppend Int.add (Int.subNatNat p q) (invalid.terms weight r size s) (List.concatMap (invalid.terms weight r size) (List.rangeFrom c (Succ s))))
      (Eq.trans (Eq.cong (\a => List.foldLeft Int.add a (List.concatMap (invalid.terms weight r size) (List.rangeFrom c (Succ s)))) (termsFold r s size (zero s hs) 9 2 rfl p q))
        (Eq.trans (kFold r size zero c (Succ s) (Nat.leTrans 1 s (Succ s) hs (Nat.leSucc s))
            (List.sumBy (\n => Nat.keepIf (repeated r s n) (plus n)) (List.rangeFrom 9 2) + p) (List.sumBy (\n => Nat.keepIf (repeated r s n) (minus n)) (List.rangeFrom 9 2) + q))
          (Eq.sym (consSub (\k => List.sumBy (\n => Nat.keepIf (repeated r k n) (plus n)) (List.rangeFrom 9 2)) (\k => List.sumBy (\n => Nat.keepIf (repeated r k n) (minus n)) (List.rangeFrom 9 2)) s (List.rangeFrom c (Succ s)) p q))))

-- A block written n times with more digits than `hi` adds nothing.
theorem repeatedZero (r: Range) (k: Nat) (hk: 1 <= k) (n: Nat) (hn: 2 <= n) (h: Nat.leq (k * n) (List.length (Nat.digits r.hi)) = False): repeated r k n = 0 :=
  Eq.trans (repeatedIds r k hk n hn)
    (List.sumRangeNone (\x => writtenAs (Nat.digits x) k n) (\x => x) r.size r.lo
      (\x x1 x2 => Bool.inspect (writtenAs (Nat.digits x) k n) (\u => u = False)
        (\t => Void.exfalso (Nat.lessIrrefl (List.length (Nat.digits r.hi))
          (Nat.leTrans (Succ (List.length (Nat.digits r.hi))) (k * n) (List.length (Nat.digits r.hi))
            (Nat.leqFalse (k * n) (List.length (Nat.digits r.hi)) h)
            (Nat.leCongLeft (List.length (Nat.digits x)) (k * n) (List.length (Nat.digits r.hi)) (Eq.sym (Eq.trans (Nat.mulComm k n) (countOf x k n hn t))) (idsBelow r x x1 x2)))))
        (\f => rfl)))

-- (2) One range's `invalid`, added to a running total.
theorem invalidSplit (r: Range) (p: Nat) (q: Nat): Int.add (Int.subNatNat p q) (invalid weight r) = Int.subNatNat (weighted plus r + p) (weighted minus r + q) :=
  Eq.trans (Eq.sym (List.sumIntFrom (Int.subNatNat p q) (List.concatMap (invalid.terms weight r (List.length (Nat.digits r.hi))) (List.rangeFrom (List.length (Nat.digits r.hi)) 1))))
    (kFold r (List.length (Nat.digits r.hi)) (repeatedZero r) (List.length (Nat.digits r.hi)) 1 rfl p q)

theorem totalSplit: (ranges: List Range) -> (p: Nat) -> (q: Nat) ->
    List.foldLeft Int.add (Int.subNatNat p q) (List.map (invalid weight) ranges) = Int.subNatNat (List.sumBy (weighted plus) ranges + p) (List.sumBy (weighted minus) ranges + q)
  | Nil,       p, q => rfl
  | Cons r rs, p, q =>
    Eq.trans (Eq.cong (\a => List.foldLeft Int.add a (List.map (invalid weight) rs)) (invalidSplit r p q))
      (Eq.trans (totalSplit rs (weighted plus r + p) (weighted minus r + q))
        (Eq.sym (consSub (weighted plus) (weighted minus) r rs p q)))

-- Part 2 is right -------------------------------------------------------------

-- The puzzle's method: in every range walk the ids, keep those whose digits
-- are some block written two or more times, add them up.
def part2Spec (ranges: List Range): Nat :=
  ranges |> .sumBy (\r => r.ids |> .filter repeats |> .sum)

test "part 2 spec" := part2Spec exampleRanges == 4174379265

-- Part 2 is the sum of the ids, in all the ranges, whose digits are some
-- block written two or more times, when every id has at most 10 digits.
theorem part2Correct (ranges: List Range) (small: List.all fits ranges = True): solvePart2 ranges = part2Spec ranges :=
  calc solvePart2 ranges
    _ = Int.toNat (Int.subNatNat (List.sumBy (weighted plus) ranges + 0) (List.sumBy (weighted minus) ranges + 0)) := Eq.cong Int.toNat (totalSplit ranges 0 0)
    _ = Int.toNat (Int.subNatNat (List.sumBy (weighted plus) ranges) (List.sumBy (weighted minus) ranges)) :=
      Eq.cong Int.toNat (subCong _ _ _ _ (Nat.addZero (List.sumBy (weighted plus) ranges)) (Nat.addZero (List.sumBy (weighted minus) ranges)))
    _ = Int.toNat (Int.subNatNat (List.sumBy (\r => List.sum (List.filter repeats (Range.ids r)) + weighted minus r) ranges) (List.sumBy (weighted minus) ranges)) :=
      Eq.cong (\t => Int.toNat (Int.subNatNat t (List.sumBy (weighted minus) ranges)))
        (List.sumByCongrAll fits (weighted plus) (\r => List.sum (List.filter repeats (Range.ids r)) + weighted minus r) rangeSplit ranges small)
    _ = Int.toNat (Int.subNatNat (part2Spec ranges + List.sumBy (weighted minus) ranges) (List.sumBy (weighted minus) ranges)) :=
      Eq.cong (\t => Int.toNat (Int.subNatNat t (List.sumBy (weighted minus) ranges))) (List.sumByAdd (\r => List.sum (List.filter repeats (Range.ids r))) (weighted minus) ranges)
    _ = part2Spec ranges := Int.toNatSubNatNat (part2Spec ranges) (List.sumBy (weighted minus) ranges)

-- The ranges `parseRanges` gives back all fit.
theorem allFit (ranges: List Range) (rs: List Range) (h: ifAllFit ranges = Just rs): List.all fits rs = True :=
  Bool.inspect (List.all fits ranges)
    (\u => Bool.ifThenElse u (\v => Just ranges) (\v => Nothing) = Just rs -> List.all fits rs = True)
    (\t e => J (\l q => List.all fits l = True) t (Eq.cong (Maybe.withDefault ranges) e))
    (\f e => Void.exfalso (Maybe.nothingNotJust rs e))
    h

-- So for every input the program accepts, part 2 is the puzzle's sum.
theorem part2CorrectParsed (t: Text) (rs: List Range) (h: parseRanges t = Just rs): solvePart2 rs = part2Spec rs :=
  part2Correct rs (allFit (t.trim.split ',' |> .mapMaybe Range.parse) rs h)
