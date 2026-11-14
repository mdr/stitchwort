--| Day 2, why `RepetitionTemplate.sumIn` is right: the arithmetic sum of the
--| ids that are a k-digit block written n times equals the brute-force sum over
--| blocks (`repeatedCorrect`), and for any n >= 2 the sum over the ids
--| themselves (`repeatedIds`); over the block lengths, an id counts once
--| (`collapse`). The repetition facts are proved once here, for n copies;
--| Part1.sw uses them at n = 2 and Part2.sw for every n.
--
-- Kept apart from the program, so
-- `stitchwort run Aoc.Year2025.Day02.main` doesn't check it.

namespace Aoc.Year2025.Day02.Proofs
import Aoc.Common (..)
import Aoc.Common.Proofs (..)
import Aoc.Year2025.Day02 (..)
import Aoc.Year2025.Day02.Spec (..)
import Std (Bool, DecEq, Decidable, Eq, List, Nat, Void)

-- Why `RepetitionTemplate.sumIn` is right (a):
-- `RepetitionTemplate.sumIn template r` equals `repeatedSpec r k n`, the
-- brute-force sum below, for every range, block length and repeat count.
--
-- The outline: writing a block `b` n times gives `b * m` (`writeTimesMul`);
-- `from <= b * m <= to` exactly when `b` is between `from / m` rounded up and
-- `to / m` rounded down (`Nat.roundUpLe` and friends); so the ids in the range
-- are `m` times an interval of blocks (`window`), whose sum is Gauss's formula
-- (`List.gaussSum`).

--| The specification. `writeTimes k b n` is the block `b` written `n` times:
--| each copy shifts the ones before it left by `k` digits (`b` has `k` digits).
def writeTimes (k b: Nat): Nat → Nat
  | Zero => 0
  | Succ n => writeTimes k b n * Nat.pow 10 k + b

--| Brute force: write every k-digit block n times, keep the ids inside the
--| range, and add them up. It walks the blocks rather than the ids, but it
--| counts the same ids: each id that is a block written n times is so for just
--| one block (its first k digits).
def repeatedSpec (r: Range) (k n: Nat): Nat :=
  List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))
    |> .map (b => writeTimes k b n)
    |> .filter (x => r.from ≤ x ≤ r.to)
    |> .sum

--| `RepetitionTemplate.sumIn` with its parts as parameters: the multiplier `m`, the
--| smallest block `low` and the first number too long to be a block `p`.
def multiplier (k n: Nat): Nat := List.range 0 n |> .sumBy (i => Nat.pow 10 (k * i))

def blocksAt (r: Range) (low p m: Nat): Nat :=
  if m ≠ 0 then
    let from := Nat.max low (Nat.ceilDiv r.from m)
    let to := Nat.min (p - 1) (r.to / m)
    m * Nat.sumBetween from to
  else 0

theorem repeatedAt ∀ (r: Range) (k n: Nat):
    RepetitionTemplate.sumIn { blockLength = k, copies = n } r
      = blocksAt r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (multiplier k n) :=
  rfl

--| The multiplier: writing `b` n times is `b * multiplier k n`.
theorem multiplierSucc ∀ (k n: Nat): multiplier k (Succ n) = 1 + Nat.pow 10 k * multiplier k n := calc multiplier k
  (Succ n)
  _ = Nat.pow 10 (k * 0) + List.sumBy (List.rangeFrom n 1) (i => Nat.pow 10 (k * i)) :=
    List.sumByCons (List.rangeFrom n 1) 0 (i => Nat.pow 10 (k * i))
  _ = 1 + List.sumBy (List.rangeFrom n 1) (i => Nat.pow 10 (k * i)) := rewrite (ring: k * 0 = 0)
  _ = 1 + List.sumBy (List.range 0 n) (i => Nat.pow 10 (k * Succ i)) :=
    rewrite List.sumByRangeShift (i => Nat.pow 10 (k * i)) n 0
  _ = 1 + List.sumBy (List.range 0 n) (i => Nat.pow 10 k * Nat.pow 10 (k * i)) :=
    rewrite Nat.mulSucc k _, Nat.powAdd 10 k _
  _ = 1 + Nat.pow 10 k * multiplier k n :=
    rewrite List.sumByMulLeft (List.range 0 n) (Nat.pow 10 k) (i => Nat.pow 10 (k * i))

theorem writeTimesMul ∀ (k b n: Nat): writeTimes k b n = b * multiplier k n := match n with
  | Zero => ring
  | Succ n => rewrite writeTimesMul k b n, multiplierSucc k n in ring

--| The ids `b * d` for `b` from `s` to `s + c - 1` that lie in `from..to`, added up.
def windowSum (from to d c s: Nat): Nat :=
  List.sum (List.filter (List.map (List.rangeFrom c s) (b => b * d)) (x => from ≤ x ≤ to))

theorem specWindow ∀ (r: Range) (k n: Nat):
    repeatedSpec r k n
      = windowSum r.from r.to (multiplier k n) (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)) :=
  rewrite writeTimesMul k _ n

--| With a multiplier of 0 every id is 0.
theorem windowZero ∀ (from to c s: Nat): windowSum from to 0 c s = 0 := match c with
  | Zero => rfl
  | Succ c =>
    match h: (from ≤ s * 0 ≤ to) with
      | True => rewrite (ring: s * 0 = 0) in windowZero from to c (Succ s)
      | False => windowZero from to c (Succ s)

--| One step of `window`, for each place `s` can be: below `bLo`, in `bLo..bHi`, above `bHi`.
theorem windowBelow ∀ (from to d bLo bHi c s: Nat)
    (no: Nat.leq from (s * d) = False)
    (hs: Succ s ≤ bLo)
    (ih: windowSum from to d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum from to d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  calc windowSum from to d (Succ c) s
    _ = windowSum from to d c (Succ s) :=
      Eq.cong List.sum
        (List.filterSkip
          (List.map (List.rangeFrom c (Succ s)) (b => b * d))
          (x => from ≤ x ≤ to)
          (s * d)
          (Nat.betweenBelow from to (s * d) no))
    _ = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi)) := ih
    _ = d * Nat.span bLo (Nat.min (Succ s + c) (Succ bHi)) := rewrite (omega: Nat.max (Succ s) bLo = bLo)
    _ = d * Nat.span bLo (Nat.min (s + Succ c) (Succ bHi)) := rewrite (ring: s + Succ c = Succ s + c)
    _ = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) := rewrite (omega: Nat.max s bLo = bLo)

theorem windowIn ∀ (from to d bLo bHi c s: Nat)
    (yes: (from ≤ s * d ≤ to) = True)
    (hA: bLo ≤ s)
    (hB: s ≤ bHi)
    (ih: windowSum from to d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum from to d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  calc windowSum from to d (Succ c) s
    _ = s * d + windowSum from to d c (Succ s) :=
      Eq.trans
        (Eq.cong List.sum
          (List.filterKeep (List.map (List.rangeFrom c (Succ s)) (b => b * d)) (x => from ≤ x ≤ to) (s * d) yes))
        (List.sumCons (s * d) (List.filter (List.map (List.rangeFrom c (Succ s)) (b => b * d)) (x => from ≤ x ≤ to)))
    _ = s * d + d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi)) := rewrite ih
    _ = s * d + d * Nat.span (Succ s) (Nat.min (Succ s + c) (Succ bHi)) :=
      rewrite (omega: Nat.max (Succ s) bLo = Succ s)
    _ = d * (s + Nat.span (Succ s) (Nat.min (Succ s + c) (Succ bHi))) := ring
    _ = d * Nat.span s (Nat.min (Succ s + c) (Succ bHi)) :=
      rewrite <- Nat.spanStep s (Nat.min (Succ s + c) (Succ bHi)) (Nat.leMin (Succ s) (Succ s + c) (Succ bHi) omega hB)
    _ = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
      rewrite (omega: Nat.max s bLo = s), (ring: s + Succ c = Succ s + c)

theorem windowAbove ∀ (from to d bLo bHi c s: Nat)
    (low: from ≤ s * d)
    (no: Nat.leq (s * d) to = False)
    (hs: Succ bHi ≤ s)
    (ih: windowSum from to d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum from to d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  calc windowSum from to d (Succ c) s
    _ = windowSum from to d c (Succ s) :=
      Eq.cong List.sum
        (List.filterSkip
          (List.map (List.rangeFrom c (Succ s)) (b => b * d))
          (x => from ≤ x ≤ to)
          (s * d)
          (Nat.betweenAbove from to (s * d) low no))
    _ = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi)) := ih
    _ = d * 0 :=
      rewrite Nat.spanEmpty
        (Nat.max (Succ s) bLo)
        (Nat.min (Succ s + c) (Succ bHi))
        (omega [Nat.minLeRight (Succ s + c) (Succ bHi)])
    _ = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
      rewrite Nat.spanEmpty (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) omega

--| The heart of it: if `from <= b * d` exactly when `bLo <= b`, and `b * d <= to`
--| exactly when `b <= bHi`, then the ids `b * d` in `from..to` for `b` in a run of
--| `c` numbers from `s` are `d` times the sum of the run cut down to `bLo..bHi`.
theorem window ∀ (from to d bLo bHi: Nat)
    (yesA: ∀ (b: Nat) => bLo ≤ b → from ≤ b * d)
    (noA: ∀ (b: Nat) => Nat.leq bLo b = False → Nat.leq from (b * d) = False)
    (yesB: ∀ (b: Nat) => b ≤ bHi → b * d ≤ to)
    (noB: ∀ (b: Nat) => Nat.leq b bHi = False → Nat.leq (b * d) to = False) (c s: Nat):
    windowSum from to d c s = d * Nat.span (Nat.max s bLo) (Nat.min (s + c) (Succ bHi)) :=
  match c with
    | Zero => rewrite Nat.spanEmpty (Nat.max s bLo) (Nat.min (s + 0) (Succ bHi)) omega in ring
    | Succ c =>
      match hA: Nat.leq bLo s, hB: Nat.leq s bHi with
        | True, True =>
          windowIn from to d bLo bHi c s
            (Nat.betweenYes from to (s * d) (yesA s hA) (yesB s hB))
            hA
            hB
            (window from to d bLo bHi yesA noA yesB noB c (Succ s))
        | True, False =>
          windowAbove from to d bLo bHi c s
            (yesA s hA)
            (noB s hB)
            omega
            (window from to d bLo bHi yesA noA yesB noB c (Succ s))
        | False, _ =>
          windowBelow from to d bLo bHi c s (noA s hA) omega (window from to d bLo bHi yesA noA yesB noB c (Succ s))

--| The sum at the end of `blocksAt`, after its `let`s, as a `Nat.span`; 0
--| when from > to, so no case split.
theorem sumBetweenSpan ∀ (d from to: Nat): d * from.sumBetween to = d * Nat.span from (Succ to) :=
  Eq.cong
    (t => d * t)
    (Eq.trans
      (Nat.sumBetweenCorrect from to)
      (Eq.cong (t => List.sum (List.rangeFrom (t - from) from)) (ring: to + 1 = Succ to)))

theorem blocksWindow ∀ (r: Range) (low: Nat):
    ∀ (p: Nat) => 0 < p → low ≤ p → ∀ (m: Nat) => blocksAt r low p m = windowSum r.from r.to m (p - low) low
  | Zero, hp, hl, m => cases
  | Succ p, hp, hl, Zero => Eq.sym (windowZero r.from r.to (Succ p - low) low)
  | Succ p, hp, hl, Succ m =>
    calc blocksAt r low (Succ p) (Succ m)
      _ = Succ m * Nat.span (Nat.max low (Nat.ceilDiv r.from (Succ m))) (Succ (Nat.min p (r.to / Succ m))) :=
        sumBetweenSpan (Succ m) (Nat.max low (Nat.ceilDiv r.from (Succ m))) (Nat.min p (r.to / Succ m))
      _ = Succ m * Nat.span (Nat.max low (Nat.ceilDiv r.from (Succ m))) (Nat.min (Succ p) (Succ (r.to / Succ m))) :=
        rewrite Nat.minSucc p (r.to / Succ m)
      _ = Succ m
          * Nat.span
            (Nat.max low (Nat.ceilDiv r.from (Succ m)))
            (Nat.min (low + (Succ p - low)) (Succ (r.to / Succ m))) := rewrite (omega: low + (Succ p - low) = Succ p)
      _ = windowSum r.from r.to (Succ m) (Succ p - low) low :=
        Eq.sym
          (window r.from r.to
            (Succ m)
            (Nat.ceilDiv r.from (Succ m))
            (r.to / Succ m)
            (b h => Nat.leMulOfCeilDivLe r.from b (Succ m) h)
            (Nat.roundUpNo r.from m)
            (b h => Nat.mulLeOfLeDiv b r.to (Succ m) h)
            (Nat.roundDownNo r.to m)
            (Succ p - low)
            low)

--| (a) The arithmetic sum is the brute-force one.
theorem repeatedCorrect ∀ (r: Range) (k n: Nat):
    RepetitionTemplate.sumIn { blockLength = k, copies = n } r = repeatedSpec r k n :=
  Eq.trans
    (blocksWindow r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (Nat.powSuccPos 9 k) (Nat.powTenPredLe k) (multiplier k n))
    (Eq.sym (specWindow r k n))

-- Why `RepetitionTemplate.sumIn` is right (b), for any number of copies
-- n >= 2: `repeatedIds` says `template.sumIn r`, for the template k by
-- n, is the sum the puzzle describes, walking the ids of the range and keeping
-- those whose digits are some k-digit block written n times (any k from 1
-- on). Part 1 uses it at n = 2, Part 2 for every n.
--
-- The outline: `repeatedSpec` walks blocks, so swap the order of the two sums
-- (`blocksAsIds`): for each id `x`, add `x` once for each k-digit block that
-- written n times makes `x`. That is one block when x's digits are a k-digit
-- block written n times, the block being x's first k digits (`repValue`),
-- and none otherwise, since a k-digit block written n times has digits that
-- are a k-digit block written n times (`repDigits`).

--| The digits `p` written n times make `fromDigits p` written n times.
theorem fromDigitsRep ∀ (p: List Nat) (n: Nat):
    Nat.fromDigits (List.concat (List.replicate n p)) = writeTimes p.length (Nat.fromDigits p) n :=
  match n with
    | Zero => rfl
    | Succ n =>
      calc Nat.fromDigits (List.concat (List.replicate (Succ n) p))
        _ = Nat.fromDigits (List.append (List.concat (List.replicate n p)) p) :=
          Eq.cong Nat.fromDigits (List.concatReplicateSnoc p n)
        _ = Nat.fromDigits (List.concat (List.replicate n p)) * Nat.pow 10 p.length + Nat.fromDigits p :=
          Nat.fromDigitsAppend (List.concat (List.replicate n p)) p
        _ = writeTimes p.length (Nat.fromDigits p) n * Nat.pow 10 p.length + Nat.fromDigits p :=
          rewrite fromDigitsRep p n

theorem repAppend ∀ (x k n: Nat)
    (hq: writtenAs x.digits.toList k n = True):
    List.concat (List.replicate n (x.digits.toList.take k)) = x.digits.toList :=
  hq.read

--| Two or more copies of a k-digit block fill the digits: there are n * k.
theorem repCount ∀ (x k n: Nat) (hn: 2 ≤ n) (hq: writtenAs x.digits.toList k n = True): n * k = x.digitCount :=
  -- The digits are n copies of their first k digits, so there are n times as many.
  let counted: n * List.length (List.take (Nat.digits x).toList k) = List.length (Nat.digits x).toList :=
    Eq.trans
      (Eq.sym (List.lengthConcatReplicate (List.take (Nat.digits x).toList k) n))
      (Eq.cong List.length (repAppend x k n hq))
  rewrite Nat.digitCountLength x in
    match room: Nat.leq k (List.length (Nat.digits x).toList) with
      -- There are k digits to take, so that is how many the first block has.
      | True => rewrite List.lengthTake (Nat.digits x).toList k room at counted
      -- Taking more digits than there are takes all of them: then n times as
      -- many digits as there are would be as many as there are, which two or
      -- more copies can't be.
      | False =>
        let sameCount: n * List.length (Nat.digits x).toList = List.length (Nat.digits x).toList :=
          rewrite List.takeAll (Nat.digits x).toList k omega at counted
        omega [Nat.leMulRight 2 n (List.length (Nat.digits x).toList) hn]

--| So the block is no longer than the digits, and is k digits long.
theorem blockAtMost ∀ (x k n: Nat) (hn: 2 ≤ n) (hq: writtenAs x.digits.toList k n = True): k ≤ x.digitCount :=
  omega [Nat.leMulPos k n omega, repCount x k n hn hq]

theorem repBlockLength ∀ (x k n: Nat)
    (hn: 2 ≤ n)
    (hq: writtenAs x.digits.toList k n = True):
    (x.digits.toList.take k).length = k :=
  List.lengthTake (Nat.digits x).toList k (omega [blockAtMost x k n hn hq, Nat.digitCountLength x])

--| x is its first k digits written n times.
theorem repValue ∀ (x k n: Nat)
    (hn: 2 ≤ n)
    (hq: writtenAs x.digits.toList k n = True):
    writeTimes k (Nat.fromDigits (x.digits.toList.take k)) n = x :=
  calc writeTimes k (Nat.fromDigits (List.take (Nat.digits x).toList k)) n
    _ = writeTimes
        (List.length (List.take (Nat.digits x).toList k))
        (Nat.fromDigits (List.take (Nat.digits x).toList k))
        n :=
      Eq.cong
        (t => writeTimes t (Nat.fromDigits (List.take (Nat.digits x).toList k)) n)
        (Eq.sym (repBlockLength x k n hn hq))
    _ = Nat.fromDigits (List.concat (List.replicate n (List.take (Nat.digits x).toList k))) :=
      Eq.sym (fromDigitsRep (List.take (Nat.digits x).toList k) n)
    _ = Nat.fromDigits (Nat.digits x).toList := Eq.cong Nat.fromDigits (repAppend x k n hq)
    _ = x := Nat.fromDigitsDigits x

--| Two or more copies of at least one digit: x isn't 0.
theorem posOfCount ∀ (n: Nat) (hn: 2 ≤ n) (x k: Nat) (hk: 1 ≤ k) (e: n * k = x.digitCount): 1 ≤ x := match x with
  | Zero => omega [Nat.leMulRight 2 n k hn]
  | Succ x => rfl

--| The block x starts with has k digits: it is below 10^k, and (no leading
--| 0) at least 10^(k-1).
theorem repBelow ∀ (x k n: Nat)
    (hn: 2 ≤ n)
    (hq: writtenAs x.digits.toList k n = True):
    Nat.fromDigits (x.digits.toList.take k) < Nat.pow 10 k :=
  calc Nat.fromDigits (List.take (Nat.digits x).toList k)
    _ < Nat.pow 10 (List.length (List.take (Nat.digits x).toList k)) :=
      Nat.fromDigitsBound
        (List.take (Nat.digits x).toList k)
        (Nat.digitsTake k (Nat.digits x).toList (Nat.digitsDigits x))
    _ = Nat.pow 10 k := rewrite repBlockLength x k n hn hq

theorem repAbove ∀ (x k n: Nat)
    (hk: 1 ≤ k)
    (hn: 2 ≤ n)
    (hq: writtenAs x.digits.toList k n = True):
    Nat.pow 10 (k - 1) ≤ Nat.fromDigits (x.digits.toList.take k) :=
  J
    (t q => Nat.pow 10 (t - 1) ≤ Nat.fromDigits (List.take (Nat.digits x).toList k))
    (Nat.fromDigitsHeadBound
      (List.take (Nat.digits x).toList k)
      (omega [
        List.headTake (Nat.digits x).toList 0 k hk,
        Nat.digitsHead x (posOfCount n hn x k hk (repCount x k n hn hq))
      ]))
    (repBlockLength x k n hn hq)

--| The other way: a block of k digits (no leading 0) written n >= 1 times
--| has those digits n times.
theorem writeTimesPos ∀ (k b: Nat) (hb: 1 ≤ b) (n: Nat): 1 ≤ writeTimes k b (Succ n) := omega

theorem digitsRep ∀ (b: Nat)
    (hb: 1 ≤ b) (n: Nat):
    (writeTimes b.digitCount b (Succ n)).digits.toList = List.concat (List.replicate (Succ n) b.digits.toList) :=
  match n with
    | Zero => Eq.sym (List.appendNil (Nat.digits b).toList)
    | Succ n =>
      calc (Nat.digits (writeTimes b.digitCount b (Succ n) * Nat.pow 10 b.digitCount + b)).toList
        _ = (Nat.digits
            (writeTimes b.digitCount b (Succ n) * Nat.pow 10 b.digitCount
              + Nat.fromDigits (Nat.digits b).toList)).toList := rewrite Nat.fromDigitsDigits b
        _ = List.append (writeTimes b.digitCount b (Succ n)).digits.toList (Nat.digits b).toList :=
          Eq.trans
            (Eq.cong
              (m =>
                (Nat.digits
                  (writeTimes b.digitCount b (Succ n) * Nat.pow 10 m + Nat.fromDigits (Nat.digits b).toList)).toList)
              (Nat.digitCountLength b))
            (Nat.digitsShift
              (Nat.digits b).toList
              (writeTimes b.digitCount b (Succ n))
              (writeTimesPos b.digitCount b hb n)
              (Nat.digitsDigits b))
        _ = List.append (List.concat (List.replicate (Succ n) (Nat.digits b).toList)) (Nat.digits b).toList :=
          Eq.cong (l => List.append l (Nat.digits b).toList) (digitsRep b hb n)
        _ = List.concat (List.replicate (Succ (Succ n)) (Nat.digits b).toList) :=
          Eq.sym (List.concatReplicateSnoc (Nat.digits b).toList (Succ n))

theorem writtenRepOf ∀ (p: List Nat) (k: Nat)
    (hk: p.length = k) (n: Nat):
    writtenAs (List.concat (List.replicate (Succ n) p)) k (Succ n) = True :=
  (List.decEq
    (a b => Nat.decEq a b)
    (List.concat (List.replicate (Succ n) (List.take (List.concat (List.replicate (Succ n) p)) k)))
    (List.concat (List.replicate (Succ n) p))).complete
    (rewrite <- hk, List.takeAppend p (List.concat (List.replicate n p)))

theorem repDigits ∀ (j b: Nat)
    (h1: Nat.pow 10 j ≤ b)
    (h2: b < Nat.pow 10 (Succ j)) (n: Nat)
    (hn: 1 ≤ n):
    writtenAs (Nat.digits (writeTimes (Succ j) b n)).toList (Succ j) n = True :=
  match n with
    | Succ n =>
      let same: (Nat.digits (writeTimes (Succ j) b (Succ n))).toList
        = List.concat (List.replicate (Succ n) (Nat.digits b).toList) :=
        Eq.trans
          (Eq.cong (m => (Nat.digits (writeTimes m b (Succ n))).toList) (Eq.sym (Nat.digitsLength j b h1 h2)))
          (digitsRep b (omega [Nat.powSuccPos 9 j]) n)
      Eq.subst
        (l => writtenAs l (Succ j) (Succ n) = True)
        (Eq.sym same)
        (writtenRepOf
          (Nat.digits b).toList
          (Succ j)
          (Eq.trans (Eq.sym (Nat.digitCountLength b)) (Nat.digitsLength j b h1 h2))
          n)

--| Different blocks written n >= 1 times make different ids.
theorem repInjective ∀ (k b v n: Nat) (hn: 1 ≤ n) (e: writeTimes k b n = writeTimes k v n): b = v := match n with
  | Succ m =>
    Nat.mulSuccCancel b v
      (Nat.pow 10 k * multiplier k m)
      (calc b * Succ (Nat.pow 10 k * multiplier k m)
        _ = b * multiplier k (Succ m) := rewrite multiplierSucc k m
        _ = writeTimes k b (Succ m) := Eq.sym (writeTimesMul k b (Succ m))
        _ = writeTimes k v (Succ m) := e
        _ = v * multiplier k (Succ m) := writeTimesMul k v (Succ m)
        _ = v * Succ (Nat.pow 10 k * multiplier k m) := rewrite multiplierSucc k m)

--| For one id `x`, block length k and n copies: the blocks written n times
--| that make `x` add up to `x` when x's digits are a k-digit block written n
--| times, and to 0 otherwise.
theorem repBlockCount ∀ (x n: Nat)
    (hn: 2 ≤ n) (k: Nat)
    (h: 1 ≤ k):
    List.sumBy (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b =>
      x.keepIf (writeTimes k b n == x))
      = x.keepIf (writtenAs x.digits.toList k n) :=
  match k with
    | Succ j =>
      match hq: writtenAs (Nat.digits x).toList (Succ j) n with
        | True =>
          List.sumRangeFromOne
            (b => writeTimes (Succ j) b n == x)
            (b => x)
            (Nat.fromDigits (List.take (Nat.digits x).toList (Succ j)))
            ((Nat.decEq (writeTimes (Succ j) (Nat.fromDigits (List.take (Nat.digits x).toList (Succ j))) n) x).complete
              (repValue x (Succ j) n hn hq))
            (b hb =>
              repInjective
                (Succ j)
                b
                (Nat.fromDigits (List.take (Nat.digits x).toList (Succ j)))
                n
                omega
                (Eq.trans hb.read (Eq.sym (repValue x (Succ j) n hn hq))))
            (Nat.pow 10 (Succ j) - Nat.pow 10 j)
            (Nat.pow 10 j)
            (repAbove x (Succ j) n rfl hn hq)
            (omega [repBelow x (Succ j) n hn hq, Nat.powTenPredLe (Succ j)])
        | False =>
          List.sumRangeFromNone
            (b => writeTimes (Succ j) b n == x)
            (b => x)
            (Nat.pow 10 (Succ j) - Nat.pow 10 j)
            (Nat.pow 10 j)
            (b h1 h2 =>
              Decidable.toBoolOfNot (Nat.decEq (writeTimes (Succ j) b n) x) (e =>
                Bool.trueNotFalse
                  (Eq.trans (Eq.sym (rewrite e at repDigits j b h1 (omega [Nat.powTenPredLe (Succ j)]) n omega)) hq)))

--| The ids from from to to that equal `y`, added up.
theorem sumIdsEq ∀ (from to y: Nat):
    List.sumBy (List.rangeFrom (to + 1 - from) from) (x => x.keepIf (y == x)) = y.keepIf (from ≤ y ≤ to) :=
  match t: Nat.leq from y, t2: Nat.leq y to with
    | True, True => List.sumRangeFromEq y (to + 1 - from) from t (rangeIn from to y t t2)
    | True, False => List.sumRangeFromEqNone y (to + 1 - from) from (x hx1 hx2 e =>
      Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite <- e at rangeEnd from to x hx1 hx2)) t2))
    | False, _ => List.sumRangeFromEqNone y (to + 1 - from) from (x hx1 hx2 e =>
      Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite <- e at hx1)) t))

--| One block length, as a sum over the ids of the range.
theorem blocksAsIds ∀ (r: Range) (k n: Nat):
    repeatedSpec r k n
      = List.sumBy (List.rangeFrom (r.to + 1 - r.from) r.from) (x =>
        List.sumBy (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b =>
          x.keepIf (writeTimes k b n == x))) :=
  calc repeatedSpec r k n
    -- filtering the block ids by the range is summing "the id if it is in the range"
    _ = List.sumBy
        (List.map (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b => writeTimes k b n))
        (y => Nat.keepIf y (r.from ≤ y ≤ r.to)) :=
      List.sumFilter
        (List.map (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b => writeTimes k b n))
        (x => r.from ≤ x ≤ r.to)
    _ = List.sumBy (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b =>
        Nat.keepIf (writeTimes k b n) (r.from ≤ writeTimes k b n ≤ r.to)) :=
      List.sumByMap
        (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
        (y => Nat.keepIf y (r.from ≤ y ≤ r.to))
        (b => writeTimes k b n)
    -- and, for each block, "the id if it is in the range" is the sum over the range ids that equal it
    _ = List.sumBy (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b =>
        List.sumBy (List.rangeFrom (r.to + 1 - r.from) r.from) (x => Nat.keepIf x (writeTimes k b n == x))) :=
      rewrite <- sumIdsEq r.from r.to _
    _ = List.sumBy (List.rangeFrom (r.to + 1 - r.from) r.from) (x =>
        List.sumBy (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b =>
          Nat.keepIf x (writeTimes k b n == x))) :=
      List.sumBySwap
        (List.rangeFrom (r.to + 1 - r.from) r.from)
        (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
        (b x => Nat.keepIf x (writeTimes k b n == x))

--| The brute-force sum over blocks is the sum over the ids of the range whose
--| digits are a k-digit block written n times.
theorem repeatedSpecIds ∀ (r: Range) (k: Nat)
    (hk: 1 ≤ k) (n: Nat)
    (hn: 2 ≤ n):
    repeatedSpec r k n = r.ids.sumBy (x => x.keepIf (writtenAs x.digits.toList k n)) :=
  rewrite blocksAsIds r k n, repBlockCount _ n hn k hk

--| (b) `template.sumIn r`, for the template k by n, adds the ids of the
--| range whose digits are a k-digit block written n times.
theorem repeatedIds ∀ (r: Range) (k: Nat)
    (hk: 1 ≤ k) (n: Nat)
    (hn: 2 ≤ n):
    RepetitionTemplate.sumIn { blockLength = k, copies = n } r
      = r.ids.sumBy (x => x.keepIf (writtenAs x.digits.toList k n)) :=
  Eq.trans (repeatedCorrect r k n) (repeatedSpecIds r k hk n hn)

-- Over the block lengths, (c): an id is a block written n times for one
-- block length at most, n-th of its number of digits (`repCount`), so for
-- one id the sum over block lengths is the id once or not at all
-- (`collapse`). Part 1 (`doubled x` is `copies x 2`) and Part 2 both use it.

--| The digits of x are some block written n times.
def copies (x n: Nat): Bool := List.rangeFrom x.digitCount 1 |> .any (k => writtenAs (Nat.digits x).toList k n)

--| For one id and repeat count, over all block lengths up to `size`: x if
--| some block written n times makes x, else 0.
theorem collapse ∀ (x n: Nat)
    (hn: 2 ≤ n) (size: Nat)
    (hLS: x.digitCount ≤ size):
    List.sumBy (List.rangeFrom size 1) (k => x.keepIf (writtenAs x.digits.toList k n)) = x.keepIf (copies x n) :=
  match hc: copies x n with
    | True =>
      List.anyRangeElim
        (k => writtenAs (Nat.digits x).toList k n)
        (List.sumBy (List.rangeFrom size 1) (k => Nat.keepIf x (writtenAs (Nat.digits x).toList k n)) = x)
        x.digitCount
        1
        hc
        (k0 h1 h2 hk0 =>
          List.sumRangeFromOne
            (k => writtenAs (Nat.digits x).toList k n)
            (k => x)
            k0
            hk0
            (k hk => Nat.mulCancelLeft n omega k k0 (Eq.trans (repCount x k n hn hk) (Eq.sym (repCount x k0 n hn hk0))))
            size
            1
            h1
            omega)
    | False => List.sumRangeFromNone (k => writtenAs (Nat.digits x).toList k n) (k => x) size 1 (k h1 h2 =>
      match t: writtenAs (Nat.digits x).toList k n with
        | True =>
          Void.exfalso
            (Bool.trueNotFalse
              (Eq.trans
                (Eq.sym
                  (List.anyRangeIntro
                    (k => writtenAs (Nat.digits x).toList k n)
                    x.digitCount
                    1
                    k
                    h1
                    (blockAtMost x k n hn t)
                    t))
                hc))
        | False => rfl)

--| The ids of a range have at most as many digits as its end.
theorem idsBelow ∀ (r: Range) (x: Nat) (h1: r.from ≤ x) (h2: x < r.from + r.size): x.digitCount ≤ r.to.digitCount :=
  Nat.digitsLengthLe x r.to.digitCount
    (Nat.digitsNonEmpty r.to)
    (omega [rangeEnd r.from r.to x h1 h2, Nat.ltPowTenDigits r.to])
