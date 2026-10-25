-- Day 2, why `RepetitionTemplate.sumIn` is right: the arithmetic sum of the ids that are a
-- k-digit block written n times equals the brute-force sum over blocks
-- (`repeatedCorrect`), and for any n >= 2 the sum over the ids themselves
-- (`repeatedIds`); over the block lengths, an id counts once (`collapse`).
-- The repetition facts are proved once here, for n copies; Part1.sw uses
-- them at n = 2 and Part2.sw for every n. Kept apart from the program, so
-- `stitchwort run Aoc.Day02.main` doesn't check it.

namespace Aoc.Day02.Proofs
import Aoc.Common (..)
import Aoc.Common.Proofs (..)
import Aoc.Day02 (..)
import Aoc.Day02.Spec (..)
import Std (Bool, DecEq, Decidable, Eq, List, Nat, Void)

-- Why `RepetitionTemplate.sumIn` is right (a): `RepetitionTemplate.sumIn r template` equals
-- `repeatedSpec r k n`, the brute-force sum below, for every range, block
-- length and repeat count.
--
-- The outline: writing a block `b` n times gives `b * m`
-- (`writeTimesMul`); `from <= b * m <= to` exactly when `b` is between
-- `from / m` rounded up and `to / m` rounded down (`Nat.roundUpLe` and friends);
-- so the ids in the range are `m` times an interval of blocks (`window`),
-- whose sum is Gauss's formula (`List.gaussSum`).

-- The specification. `writeTimes k b n` is the block `b` written `n` times:
-- each copy shifts the ones before it left by `k` digits (`b` has `k` digits).
def writeTimes (k: Nat) (b: Nat): Nat -> Nat
  | Zero => 0
  | Succ n => writeTimes k b n * Nat.pow 10 k + b

-- Brute force: write every k-digit block n times, keep the ids inside the
-- range, and add them up. It walks the blocks rather than the ids, but it
-- counts the same ids: each id that is a block written n times is so for just
-- one block (its first k digits).
def repeatedSpec (r: Range) (k: Nat) (n: Nat): Nat :=
  List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))
    |> .map (b => writeTimes k b n)
    |> .filter (x => r.from <= x && x <= r.to)
    |> .sum

-- `RepetitionTemplate.sumIn` with its parts as parameters: the multiplier `m`, the
-- smallest block `low` and the first number too long to be a block `p`.
def multiplier (k: Nat) (n: Nat): Nat := List.range n |> .sumBy (i => Nat.pow 10 (k * i))

def blocksAt (r: Range) (low: Nat) (p: Nat) (m: Nat): Nat :=
  if m != 0 then
    let from := Nat.max low (Nat.ceilDiv r.from m)
    let to := Nat.min (p - 1) (r.to / m)
    m * Nat.sumBetween from to
  else 0

theorem repeatedAt (r: Range) (k: Nat) (n: Nat): RepetitionTemplate.sumIn r { blockLength = k, copies = n } = blocksAt r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (multiplier k n) := rfl

-- The multiplier: writing `b` n times is `b * multiplier k n`.
theorem multiplierSucc (k: Nat) (n: Nat): multiplier k (Succ n) = 1 + Nat.pow 10 k * multiplier k n :=
  calc multiplier k (Succ n)
    _ = Nat.pow 10 (k * 0) + List.sumBy (List.rangeFrom n 1) (i => Nat.pow 10 (k * i))
      := List.sumByCons (List.rangeFrom n 1) 0 (i => Nat.pow 10 (k * i))
    _ = 1 + List.sumBy (List.rangeFrom n 1) (i => Nat.pow 10 (k * i)) := rewrite (ring: k * 0 = 0)
    _ = 1 + List.sumBy (List.range n) (i => Nat.pow 10 (k * Succ i)) := rewrite List.sumByRangeShift (i => Nat.pow 10 (k * i)) n 0
    _ = 1 + List.sumBy (List.range n) (i => Nat.pow 10 k * Nat.pow 10 (k * i))
      := rewrite Nat.mulSucc k _, Nat.powAdd 10 k _
    _ = 1 + Nat.pow 10 k * multiplier k n := rewrite List.sumByMulLeft (List.range n) (Nat.pow 10 k) (i => Nat.pow 10 (k * i))

theorem writeTimesMul (k: Nat) (b: Nat): (n: Nat) -> writeTimes k b n = b * multiplier k n
  | Zero => ring
  | Succ n => rewrite writeTimesMul k b n, multiplierSucc k n in ring

-- The ids `b * d` for `b` from `s` to `s + c - 1` that lie in `from..to`, added up.
def windowSum (from: Nat) (to: Nat) (d: Nat) (c: Nat) (s: Nat): Nat :=
  List.sum (List.filter (List.map (List.rangeFrom c s) (b => b * d)) (x => from <= x && x <= to))

theorem specWindow (r: Range) (k: Nat) (n: Nat):
    repeatedSpec r k n = windowSum r.from r.to (multiplier k n) (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)) :=
  rewrite writeTimesMul k _ n

-- With a multiplier of 0 every id is 0.
theorem windowZero (from: Nat) (to: Nat): (c: Nat) -> (s: Nat) -> windowSum from to 0 c s = 0
  | Zero, s => rfl
  | Succ c, s =>
    match h: (from <= s * 0 && s * 0 <= to) with
      | True => rewrite (ring: s * 0 = 0) in windowZero from to c (Succ s)
      | False => windowZero from to c (Succ s)

-- One step of `window`, for each place `s` can be: below `bLo`, in `bLo..bHi`, above `bHi`.
theorem windowBelow (from: Nat) (to: Nat) (d: Nat) (bLo: Nat) (bHi: Nat) (c: Nat) (s: Nat)
    (no: Nat.leq from (s * d) = False) (hs: Succ s <= bLo)
    (ih: windowSum from to d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum from to d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  calc windowSum from to d (Succ c) s
    _ = windowSum from to d c (Succ s)
      := Eq.cong List.sum (List.filterSkip (List.map (List.rangeFrom c (Succ s)) (b => b * d)) (x => from <= x && x <= to) (s * d) (Nat.betweenBelow from to (s * d) no))
    _ = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi)) := ih
    _ = d * Nat.span bLo (Nat.min (Succ s + c) (Succ bHi)) := rewrite (omega: Nat.max (Succ s) bLo = bLo)
    _ = d * Nat.span bLo (Nat.min (s + Succ c) (Succ bHi)) := rewrite (ring: s + Succ c = Succ s + c)
    _ = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) := rewrite (omega: Nat.max s bLo = bLo)

theorem windowIn (from: Nat) (to: Nat) (d: Nat) (bLo: Nat) (bHi: Nat) (c: Nat) (s: Nat)
    (yes: (from <= s * d && s * d <= to) = True) (hA: bLo <= s) (hB: s <= bHi)
    (ih: windowSum from to d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum from to d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  calc windowSum from to d (Succ c) s
    _ = s * d + windowSum from to d c (Succ s)
      := Eq.trans (Eq.cong List.sum (List.filterKeep (List.map (List.rangeFrom c (Succ s)) (b => b * d)) (x => from <= x && x <= to) (s * d) yes))
        (List.sumCons (s * d) (List.filter (List.map (List.rangeFrom c (Succ s)) (b => b * d)) (x => from <= x && x <= to)))
    _ = s * d + d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi)) := rewrite ih
    _ = s * d + d * Nat.span (Succ s) (Nat.min (Succ s + c) (Succ bHi))
      := rewrite (omega: Nat.max (Succ s) bLo = Succ s)
    _ = d * (s + Nat.span (Succ s) (Nat.min (Succ s + c) (Succ bHi))) := ring
    _ = d * Nat.span s (Nat.min (Succ s + c) (Succ bHi))
      := rewrite <- Nat.spanStep s (Nat.min (Succ s + c) (Succ bHi)) (Nat.leMin (Succ s) (Succ s + c) (Succ bHi) omega hB)
    _ = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) := rewrite (omega: Nat.max s bLo = s), (ring: s + Succ c = Succ s + c)

theorem windowAbove (from: Nat) (to: Nat) (d: Nat) (bLo: Nat) (bHi: Nat) (c: Nat) (s: Nat)
    (low: from <= s * d) (no: Nat.leq (s * d) to = False) (hs: Succ bHi <= s)
    (ih: windowSum from to d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum from to d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  calc windowSum from to d (Succ c) s
    _ = windowSum from to d c (Succ s)
      := Eq.cong List.sum (List.filterSkip (List.map (List.rangeFrom c (Succ s)) (b => b * d)) (x => from <= x && x <= to) (s * d) (Nat.betweenAbove from to (s * d) low no))
    _ = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi)) := ih
    _ = d * 0
      := rewrite Nat.spanEmpty (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))
        (omega [Nat.minLeRight (Succ s + c) (Succ bHi)])
    _ = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi))
      := rewrite Nat.spanEmpty (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi))
        omega

-- The heart of it: if `from <= b * d` exactly when `bLo <= b`, and `b * d <= to`
-- exactly when `b <= bHi`, then the ids `b * d` in `from..to` for `b` in a run of
-- `c` numbers from `s` are `d` times the sum of the run cut down to `bLo..bHi`.
theorem window (from: Nat) (to: Nat) (d: Nat) (bLo: Nat) (bHi: Nat)
    (yesA: (b: Nat) -> bLo <= b -> from <= b * d)
    (noA: (b: Nat) -> Nat.leq bLo b = False -> Nat.leq from (b * d) = False)
    (yesB: (b: Nat) -> b <= bHi -> b * d <= to)
    (noB: (b: Nat) -> Nat.leq b bHi = False -> Nat.leq (b * d) to = False):
    (c: Nat) -> (s: Nat) -> windowSum from to d c s = d * Nat.span (Nat.max s bLo) (Nat.min (s + c) (Succ bHi))
  | Zero, s =>
    rewrite Nat.spanEmpty (Nat.max s bLo) (Nat.min (s + 0) (Succ bHi)) omega in ring
  | Succ c, s =>
    match hA: Nat.leq bLo s, hB: Nat.leq s bHi with
      | True, True =>
        windowIn from to d bLo bHi c s (Nat.betweenYes from to (s * d) (yesA s hA) (yesB s hB)) hA hB
          (window from to d bLo bHi yesA noA yesB noB c (Succ s))
      | True, False =>
        windowAbove from to d bLo bHi c s (yesA s hA) (noB s hB) omega
          (window from to d bLo bHi yesA noA yesB noB c (Succ s))
      | False, _ =>
        windowBelow from to d bLo bHi c s (noA s hA) omega
          (window from to d bLo bHi yesA noA yesB noB c (Succ s))

-- The sum at the end of `blocksAt`, after its `let`s, as a `Nat.span`; 0
-- when from > to, so no case split.
theorem sumBetweenSpan (d: Nat) (from: Nat) (to: Nat): d * Nat.sumBetween from to = d * Nat.span from (Succ to) :=
  Eq.cong (t => d * t)
    (Eq.trans (Nat.sumBetweenCorrect from to) (Eq.cong (t => List.sum (List.rangeFrom (t - from) from)) (ring: to + 1 = Succ to)))

theorem blocksWindow (r: Range) (low: Nat): (p: Nat) -> 0 < p -> low <= p -> (m: Nat) ->
    blocksAt r low p m = windowSum r.from r.to m (p - low) low
  | Zero, hp, hl, m => Void.exfalso (Bool.falseNotTrue hp)
  | Succ p, hp, hl, Zero => Eq.sym (windowZero r.from r.to (Succ p - low) low)
  | Succ p, hp, hl, Succ m =>
    calc blocksAt r low (Succ p) (Succ m)
      _ = Succ m * Nat.span (Nat.max low (Nat.ceilDiv r.from (Succ m))) (Succ (Nat.min p (r.to / Succ m)))
        := sumBetweenSpan (Succ m) (Nat.max low (Nat.ceilDiv r.from (Succ m))) (Nat.min p (r.to / Succ m))
      _ = Succ m * Nat.span (Nat.max low (Nat.ceilDiv r.from (Succ m))) (Nat.min (Succ p) (Succ (r.to / Succ m)))
        := rewrite Nat.minSucc p (r.to / Succ m)
      _ = Succ m * Nat.span (Nat.max low (Nat.ceilDiv r.from (Succ m))) (Nat.min (low + (Succ p - low)) (Succ (r.to / Succ m)))
        := rewrite (omega: low + (Succ p - low) = Succ p)
      _ = windowSum r.from r.to (Succ m) (Succ p - low) low
        := Eq.sym (window r.from r.to (Succ m) (Nat.ceilDiv r.from (Succ m)) (r.to / Succ m)
          (b h => Nat.leMulOfCeilDivLe r.from b (Succ m) h) (Nat.roundUpNo r.from m) (b h => Nat.mulLeOfLeDiv b r.to (Succ m) h) (Nat.roundDownNo r.to m)
          (Succ p - low) low)

-- (a) The arithmetic sum is the brute-force one.
theorem repeatedCorrect (r: Range) (k: Nat) (n: Nat): RepetitionTemplate.sumIn r { blockLength = k, copies = n } = repeatedSpec r k n :=
  Eq.trans (blocksWindow r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (Nat.powSuccPos 9 k) (Nat.powTenPredLe k) (multiplier k n))
    (Eq.sym (specWindow r k n))

-- Why `RepetitionTemplate.sumIn` is right (b), for any number of copies
-- n >= 2: `repeatedIds` says `RepetitionTemplate.sumIn r` of the template k by
-- n is the sum the puzzle describes, walking the ids of the range and keeping
-- those whose digits are some k-digit block written n times (any k from 1
-- on). Part 1 uses it at n = 2, Part 2 for every n.
--
-- The outline: `repeatedSpec` walks blocks, so swap the order of the two sums
-- (`blocksAsIds`): for each id `x`, add `x` once for each k-digit block that
-- written n times makes `x`. That is one block when x's digits are a k-digit
-- block written n times, the block being x's first k digits (`repValue`),
-- and none otherwise, since a k-digit block written n times has digits that
-- are a k-digit block written n times (`repDigits`).

-- The digits `p` written n times make `fromDigits p` written n times.
theorem fromDigitsRep (p: List Nat): (n: Nat) -> Nat.fromDigits (List.concat (List.replicate n p)) = writeTimes p.length (Nat.fromDigits p) n
  | Zero => rfl
  | Succ n =>
    calc Nat.fromDigits (List.concat (List.replicate (Succ n) p))
      _ = Nat.fromDigits (List.append (List.concat (List.replicate n p)) p) := Eq.cong Nat.fromDigits (List.concatReplicateSnoc p n)
      _ = Nat.fromDigits (List.concat (List.replicate n p)) * Nat.pow 10 p.length + Nat.fromDigits p := Nat.fromDigitsAppend (List.concat (List.replicate n p)) p
      _ = writeTimes p.length (Nat.fromDigits p) n * Nat.pow 10 p.length + Nat.fromDigits p := rewrite fromDigitsRep p n

theorem repAppend (x: Nat) (k: Nat) (n: Nat) (hq: writtenAs (Nat.digits x) k n = True):
    List.concat (List.replicate n (List.take (Nat.digits x) k)) = Nat.digits x :=
  DecEq.sound (List.concat (List.replicate n (List.take (Nat.digits x) k))) (Nat.digits x) hq

-- Two or more copies of a k-digit block fill the digits: there are n * k.
theorem repCount (x: Nat) (k: Nat) (n: Nat) (hn: 2 <= n) (hq: writtenAs (Nat.digits x) k n = True): n * k = List.length (Nat.digits x) :=
  -- The digits are n copies of their first k digits, so there are n times as many.
  let counted: n * List.length (List.take (Nat.digits x) k) = List.length (Nat.digits x) :=
    Eq.trans (Eq.sym (List.lengthConcatReplicate (List.take (Nat.digits x) k) n)) (Eq.cong List.length (repAppend x k n hq))
  match room: Nat.leq k (List.length (Nat.digits x)) with
    -- There are k digits to take, so that is how many the first block has.
    | True => rewrite List.lengthTake (Nat.digits x) k room at counted
    -- Taking more digits than there are takes all of them: then n times as
    -- many digits as there are would be as many as there are, which two or
    -- more copies can't be.
    | False =>
      let sameCount: n * List.length (Nat.digits x) = List.length (Nat.digits x) :=
        rewrite List.takeAll (Nat.digits x) k omega at counted
      omega [Nat.leMulRight 2 n (List.length (Nat.digits x)) hn, Nat.digitsNonEmpty x]

-- So the block is no longer than the digits, and is k digits long.
theorem blockAtMost (x: Nat) (k: Nat) (n: Nat) (hn: 2 <= n) (hq: writtenAs (Nat.digits x) k n = True): k <= List.length (Nat.digits x) :=
  omega [Nat.leMulPos k n omega, repCount x k n hn hq]

theorem repBlockLength (x: Nat) (k: Nat) (n: Nat) (hn: 2 <= n) (hq: writtenAs (Nat.digits x) k n = True): List.length (List.take (Nat.digits x) k) = k :=
  List.lengthTake (Nat.digits x) k (blockAtMost x k n hn hq)

-- x is its first k digits written n times.
theorem repValue (x: Nat) (k: Nat) (n: Nat) (hn: 2 <= n) (hq: writtenAs (Nat.digits x) k n = True):
    writeTimes k (Nat.fromDigits (List.take (Nat.digits x) k)) n = x :=
  calc writeTimes k (Nat.fromDigits (List.take (Nat.digits x) k)) n
    _ = writeTimes (List.length (List.take (Nat.digits x) k)) (Nat.fromDigits (List.take (Nat.digits x) k)) n
      := Eq.cong (t => writeTimes t (Nat.fromDigits (List.take (Nat.digits x) k)) n) (Eq.sym (repBlockLength x k n hn hq))
    _ = Nat.fromDigits (List.concat (List.replicate n (List.take (Nat.digits x) k))) := Eq.sym (fromDigitsRep (List.take (Nat.digits x) k) n)
    _ = Nat.fromDigits (Nat.digits x) := Eq.cong Nat.fromDigits (repAppend x k n hq)
    _ = x := Nat.fromDigitsDigits x

-- Two or more copies of at least one digit: x isn't 0.
theorem posOfCount (n: Nat) (hn: 2 <= n): (x: Nat) -> (k: Nat) -> 1 <= k -> n * k = List.length (Nat.digits x) -> 1 <= x
  | Zero, k, hk, e => omega [Nat.leMulRight 2 n k hn]
  | Succ x, k, hk, e => rfl

-- The block x starts with has k digits: it is below 10^k, and (no leading
-- 0) at least 10^(k-1).
theorem repBelow (x: Nat) (k: Nat) (n: Nat) (hn: 2 <= n) (hq: writtenAs (Nat.digits x) k n = True):
    Nat.fromDigits (List.take (Nat.digits x) k) < Nat.pow 10 k :=
  calc Nat.fromDigits (List.take (Nat.digits x) k)
    _ < Nat.pow 10 (List.length (List.take (Nat.digits x) k))
      := Nat.fromDigitsBound (List.take (Nat.digits x) k) (Nat.digitsTake k (Nat.digits x) (Nat.digitsDigits x))
    _ = Nat.pow 10 k := rewrite repBlockLength x k n hn hq

theorem repAbove (x: Nat) (k: Nat) (n: Nat) (hk: 1 <= k) (hn: 2 <= n) (hq: writtenAs (Nat.digits x) k n = True):
    Nat.pow 10 (k - 1) <= Nat.fromDigits (List.take (Nat.digits x) k) :=
  J (t q => Nat.pow 10 (t - 1) <= Nat.fromDigits (List.take (Nat.digits x) k))
    (Nat.fromDigitsHeadBound (List.take (Nat.digits x) k)
      (omega [List.headTake (Nat.digits x) 0 k hk, Nat.digitsHead x (posOfCount n hn x k hk (repCount x k n hn hq))]))
    (repBlockLength x k n hn hq)

-- The other way: a block of k digits (no leading 0) written n >= 1 times
-- has those digits n times.
theorem writeTimesPos (k: Nat) (b: Nat) (hb: 1 <= b) (n: Nat): 1 <= writeTimes k b (Succ n) :=
  omega

theorem digitsRep (b: Nat) (hb: 1 <= b): (n: Nat) ->
    Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n)) = List.concat (List.replicate (Succ n) (Nat.digits b))
  | Zero => Eq.sym (List.appendNil (Nat.digits b))
  | Succ n =>
    calc Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n) * Nat.pow 10 (List.length (Nat.digits b)) + b)
      _ = Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n) * Nat.pow 10 (List.length (Nat.digits b)) + Nat.fromDigits (Nat.digits b)) := rewrite Nat.fromDigitsDigits b
      _ = List.append (Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n))) (Nat.digits b) := Nat.digitsShift (Nat.digits b) (writeTimes (List.length (Nat.digits b)) b (Succ n)) (writeTimesPos (List.length (Nat.digits b)) b hb n) (Nat.digitsDigits b)
      _ = List.append (List.concat (List.replicate (Succ n) (Nat.digits b))) (Nat.digits b) := rewrite digitsRep b hb n
      _ = List.concat (List.replicate (Succ (Succ n)) (Nat.digits b)) := Eq.sym (List.concatReplicateSnoc (Nat.digits b) (Succ n))

theorem writtenRepOf (p: List Nat) (k: Nat) (hk: p.length = k) (n: Nat): writtenAs (List.concat (List.replicate (Succ n) p)) k (Succ n) = True :=
  Decidable.toBoolOf (List.decEq (a b => Nat.decEq a b) (List.concat (List.replicate (Succ n) (List.take (List.concat (List.replicate (Succ n) p)) k))) (List.concat (List.replicate (Succ n) p)))
    (rewrite <- hk, List.takeAppend p (List.concat (List.replicate n p)))

theorem repDigits (j: Nat) (b: Nat) (h1: Nat.pow 10 j <= b) (h2: b < Nat.pow 10 (Succ j)): (n: Nat) -> 1 <= n ->
    writtenAs (Nat.digits (writeTimes (Succ j) b n)) (Succ j) n = True
  | Zero, hn => Void.exfalso (Bool.falseNotTrue hn)
  | Succ n, hn =>
    rewrite <- (calc List.concat (List.replicate (Succ n) (Nat.digits b))
        _ = Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n))
          := Eq.sym (digitsRep b (omega [Nat.powSuccPos 9 j]) n)
        _ = Nat.digits (writeTimes (Succ j) b (Succ n)) := rewrite Nat.digitsLength j b h1 h2)
      in writtenRepOf (Nat.digits b) (Succ j) (Nat.digitsLength j b h1 h2) n

-- Different blocks written n >= 1 times make different ids.
theorem repInjective (k: Nat) (b: Nat) (v: Nat): (n: Nat) -> 1 <= n -> writeTimes k b n = writeTimes k v n -> b = v
  | Zero, hn, e => Void.exfalso (Bool.falseNotTrue hn)
  | Succ m, hn, e =>
    Nat.mulSuccCancel b v (Nat.pow 10 k * multiplier k m)
      (calc b * Succ (Nat.pow 10 k * multiplier k m)
        _ = b * multiplier k (Succ m) := rewrite multiplierSucc k m
        _ = writeTimes k b (Succ m) := Eq.sym (writeTimesMul k b (Succ m))
        _ = writeTimes k v (Succ m) := e
        _ = v * multiplier k (Succ m) := writeTimesMul k v (Succ m)
        _ = v * Succ (Nat.pow 10 k * multiplier k m) := rewrite multiplierSucc k m)

-- For one id `x`, block length k and n copies: the blocks written n times
-- that make `x` add up to `x` when x's digits are a k-digit block written n
-- times, and to 0 otherwise.
theorem repBlockCount (x: Nat) (n: Nat) (hn: 2 <= n): (k: Nat) -> 1 <= k ->
    List.sumBy (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b => Nat.keepIf x (writeTimes k b n == x))
      = Nat.keepIf x (writtenAs (Nat.digits x) k n)
  | Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ j, h =>
    match hq: writtenAs (Nat.digits x) (Succ j) n with
      | True =>
        List.sumRangeOne (b => writeTimes (Succ j) b n == x) (b => x) (Nat.fromDigits (List.take (Nat.digits x) (Succ j)))
          (Decidable.toBoolOf (Nat.decEq (writeTimes (Succ j) (Nat.fromDigits (List.take (Nat.digits x) (Succ j))) n) x) (repValue x (Succ j) n hn hq))
          (b hb => repInjective (Succ j) b (Nat.fromDigits (List.take (Nat.digits x) (Succ j))) n omega
            (Eq.trans (DecEq.sound (writeTimes (Succ j) b n) x hb) (Eq.sym (repValue x (Succ j) n hn hq))))
          (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
          (repAbove x (Succ j) n rfl hn hq)
          (omega [repBelow x (Succ j) n hn hq, Nat.powTenPredLe (Succ j)])
      | False =>
        List.sumRangeNone (b => writeTimes (Succ j) b n == x) (b => x) (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
          (b h1 h2 => Decidable.toBoolOfNot (Nat.decEq (writeTimes (Succ j) b n) x)
            (e => Bool.trueNotFalse (Eq.trans
              (Eq.sym (rewrite e at
                repDigits j b h1
                  (omega [Nat.powTenPredLe (Succ j)])
                  n omega))
              hq)))

-- The ids from from to to that equal `y`, added up.
theorem sumIdsEq (from: Nat) (to: Nat) (y: Nat):
    List.sumBy (List.rangeFrom (to + 1 - from) from) (x => Nat.keepIf x (y == x)) = Nat.keepIf y (from <= y && y <= to) :=
  match t: Nat.leq from y, t2: Nat.leq y to with
    | True, True => List.sumRangeEq y (to + 1 - from) from t (rangeIn from to y t t2)
    | True, False =>
      List.sumRangeEqNone y (to + 1 - from) from
        (x hx1 hx2 e => Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite <- e at rangeEnd from to x hx1 hx2)) t2))
    | False, _ =>
      List.sumRangeEqNone y (to + 1 - from) from
        (x hx1 hx2 e => Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite <- e at hx1)) t))

-- One block length, as a sum over the ids of the range.
theorem blocksAsIds (r: Range) (k: Nat) (n: Nat):
    repeatedSpec r k n
      = List.sumBy (List.rangeFrom (r.to + 1 - r.from) r.from)
        (x => List.sumBy (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b => Nat.keepIf x (writeTimes k b n == x))) :=
  calc repeatedSpec r k n
    -- filtering the block ids by the range is summing "the id if it is in the range"
    _ = List.sumBy (List.map (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b => writeTimes k b n)) (y => Nat.keepIf y (r.from <= y && y <= r.to))
      := List.sumFilter (List.map (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b => writeTimes k b n)) (x => r.from <= x && x <= r.to)
    _ = List.sumBy (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b => Nat.keepIf (writeTimes k b n) (r.from <= writeTimes k b n && writeTimes k b n <= r.to))
      := List.sumByMap (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (y => Nat.keepIf y (r.from <= y && y <= r.to)) (b => writeTimes k b n)
    -- and, for each block, "the id if it is in the range" is the sum over the range ids that equal it
    _ = List.sumBy (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b => List.sumBy (List.rangeFrom (r.to + 1 - r.from) r.from) (x => Nat.keepIf x (writeTimes k b n == x)))
      := rewrite <- sumIdsEq r.from r.to _
    _ = List.sumBy (List.rangeFrom (r.to + 1 - r.from) r.from) (x => List.sumBy (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b => Nat.keepIf x (writeTimes k b n == x)))
      := List.sumBySwap (List.rangeFrom (r.to + 1 - r.from) r.from) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b x => Nat.keepIf x (writeTimes k b n == x))

-- The brute-force sum over blocks is the sum over the ids of the range whose
-- digits are a k-digit block written n times.
theorem repeatedSpecIds (r: Range) (k: Nat) (hk: 1 <= k) (n: Nat) (hn: 2 <= n):
    repeatedSpec r k n = List.sumBy r.ids (x => Nat.keepIf x (writtenAs (Nat.digits x) k n)) :=
  rewrite blocksAsIds r k n, repBlockCount _ n hn k hk

-- (b) `RepetitionTemplate.sumIn r` of the template k by n adds the ids of the
-- range whose digits are a k-digit block written n times.
theorem repeatedIds (r: Range) (k: Nat) (hk: 1 <= k) (n: Nat) (hn: 2 <= n):
    RepetitionTemplate.sumIn r { blockLength = k, copies = n } = List.sumBy r.ids (x => Nat.keepIf x (writtenAs (Nat.digits x) k n)) :=
  Eq.trans (repeatedCorrect r k n) (repeatedSpecIds r k hk n hn)

-- Over the block lengths, (c): an id is a block written n times for one
-- block length at most, n-th of its number of digits (`repCount`), so for
-- one id the sum over block lengths is the id once or not at all
-- (`collapse`). Part 1 (`doubled x` is `copies x 2`) and Part 2 both use it.

-- The digits of x are some block written n times.
def copies (x: Nat) (n: Nat): Bool :=
  List.rangeFrom (Nat.digits x).length 1 |> .any (k => writtenAs (Nat.digits x) k n)

-- For one id and repeat count, over all block lengths up to `size`: x if
-- some block written n times makes x, else 0.
theorem collapse (x: Nat) (n: Nat) (hn: 2 <= n) (size: Nat) (hLS: List.length (Nat.digits x) <= size):
    List.sumBy (List.rangeFrom size 1) (k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) = Nat.keepIf x (copies x n) :=
  match hc: copies x n with
    | True =>
      List.anyRangeElim (k => writtenAs (Nat.digits x) k n) (List.sumBy (List.rangeFrom size 1) (k => Nat.keepIf x (writtenAs (Nat.digits x) k n)) = x) (List.length (Nat.digits x)) 1 hc
        (k0 h1 h2 hk0 => List.sumRangeOne (k => writtenAs (Nat.digits x) k n) (k => x) k0 hk0
          (k hk => Nat.mulCancelLeft n omega k k0 (Eq.trans (repCount x k n hn hk) (Eq.sym (repCount x k0 n hn hk0))))
          size 1 h1 omega)
    | False =>
      List.sumRangeNone (k => writtenAs (Nat.digits x) k n) (k => x) size 1
        (k h1 h2 =>
          match t: writtenAs (Nat.digits x) k n with
            | True => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (List.anyRangeIntro (k => writtenAs (Nat.digits x) k n) (List.length (Nat.digits x)) 1 k h1 (blockAtMost x k n hn t) t)) hc))
            | False => rfl)

-- The ids of a range have at most as many digits as its end.
theorem idsBelow (r: Range) (x: Nat) (h1: r.from <= x) (h2: x < r.from + r.size): List.length (Nat.digits x) <= List.length (Nat.digits r.to) :=
  Nat.digitsLengthLe x (List.length (Nat.digits r.to)) (Nat.digitsNonEmpty r.to)
    (omega [rangeEnd r.from r.to x h1 h2, Nat.ltPowTenDigits r.to])
