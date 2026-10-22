-- Day 2, why `sumWithShape` is right: the arithmetic sum of the ids that are a
-- k-digit block written n times equals the brute-force sum over blocks
-- (`repeatedCorrect`), and for n = 2 the sum over the ids themselves
-- (`repeatedTwice`). Kept apart from the program, so `stitchwort run
-- Aoc.Day02.main` doesn't check it.

namespace Aoc.Day02.Proofs
import Aoc.Common (..)
import Aoc.Common.Proofs (..)
import Aoc.Day02 (..)
import Std (Bool, Decidable, Eq, List, Nat, Void)

-- Why `sumWithShape` is right (a): `sumWithShape r shape` equals
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
  | Zero   => 0
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

-- `sumWithShape` with its parts as parameters: the multiplier `m`, the
-- smallest block `low` and the first number too long to be a block `p`.
def multiplier (k: Nat) (n: Nat): Nat := List.range n |> .sumBy (i => Nat.pow 10 (k * i))

def blocksAt (r: Range) (low: Nat) (p: Nat) (m: Nat): Nat :=
  if m != 0 then
    let from := Nat.max low ((r.from + m - 1) / m)
    let to := Nat.min (p - 1) (r.to / m)
    if from <= to then m * ((from + to) * (to - from + 1) / 2) else 0
  else 0

theorem repeatedAt (r: Range) (k: Nat) (n: Nat): sumWithShape r { blockLength = k, copies = n } = blocksAt r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (multiplier k n) := rfl

-- The multiplier: writing `b` n times is `b * multiplier k n`.
theorem multiplierSucc (k: Nat) (n: Nat): multiplier k (Succ n) = 1 + Nat.pow 10 k * multiplier k n :=
  calc multiplier k (Succ n)
    _ = Nat.pow 10 (k * 0) + List.sumBy (i => Nat.pow 10 (k * i)) (List.rangeFrom n 1)
        := List.sumByCons (i => Nat.pow 10 (k * i)) 0 (List.rangeFrom n 1)
    _ = 1 + List.sumBy (i => Nat.pow 10 (k * i)) (List.rangeFrom n 1) := rewrite Nat.mulZero k
    _ = 1 + List.sumBy (i => Nat.pow 10 (k * Succ i)) (List.range n)  := rewrite List.sumByRangeShift (i => Nat.pow 10 (k * i)) n 0
    _ = 1 + List.sumBy (i => Nat.pow 10 k * Nat.pow 10 (k * i)) (List.range n)
        := rewrite List.sumByCong (i => Nat.pow 10 (k * Succ i)) (i => Nat.pow 10 k * Nat.pow 10 (k * i))
             (List.range n) (i => Eq.trans (Eq.cong (t => Nat.pow 10 t) (Nat.mulSucc k i)) (Nat.powAdd 10 k (k * i)))
    _ = 1 + Nat.pow 10 k * multiplier k n := rewrite List.sumByMulLeft (Nat.pow 10 k) (i => Nat.pow 10 (k * i)) (List.range n)

theorem writeTimesMul (k: Nat) (b: Nat): (n: Nat) -> writeTimes k b n = b * multiplier k n
  | Zero   => Eq.sym (Nat.mulZero b)
  | Succ n =>
    calc writeTimes k b n * Nat.pow 10 k + b
      _ = b * multiplier k n * Nat.pow 10 k + b := rewrite writeTimesMul k b n
      _ = b * (multiplier k n * Nat.pow 10 k) + b := rewrite Nat.mulAssoc b (multiplier k n) (Nat.pow 10 k)
      _ = b * (Nat.pow 10 k * multiplier k n) + b := rewrite Nat.mulComm (multiplier k n) (Nat.pow 10 k)
      _ = b + b * (Nat.pow 10 k * multiplier k n) := Nat.addComm (b * (Nat.pow 10 k * multiplier k n)) b
      _ = b * 1 + b * (Nat.pow 10 k * multiplier k n) := rewrite Nat.mulOne b
      _ = b * (1 + Nat.pow 10 k * multiplier k n) := rewrite Nat.mulDistribLeft b 1 (Nat.pow 10 k * multiplier k n)
      _ = b * multiplier k (Succ n) := rewrite multiplierSucc k n

-- The ids `b * d` for `b` from `s` to `s + c - 1` that lie in `from..to`, added up.
def windowSum (from: Nat) (to: Nat) (d: Nat) (c: Nat) (s: Nat): Nat :=
  List.sum (List.filter (x => from <= x && x <= to) (List.map (b => b * d) (List.rangeFrom c s)))

theorem specWindow (r: Range) (k: Nat) (n: Nat):
    repeatedSpec r k n = windowSum r.from r.to (multiplier k n) (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)) :=
  rewrite List.mapCong (b => writeTimes k b n) (b => b * multiplier k n)
    (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))) (b => writeTimesMul k b n)

-- With a multiplier of 0 every id is 0.
theorem windowZero (from: Nat) (to: Nat): (c: Nat) -> (s: Nat) -> windowSum from to 0 c s = 0
  | Zero,   s => rfl
  | Succ c, s =>
    match h: (from <= s * 0 && s * 0 <= to) with
      | True  => rewrite Nat.mulZero s in windowZero from to c (Succ s)
      | False => windowZero from to c (Succ s)

-- One step of `window`, for each place `s` can be: below `bLo`, in `bLo..bHi`, above `bHi`.
theorem windowBelow (from: Nat) (to: Nat) (d: Nat) (bLo: Nat) (bHi: Nat) (c: Nat) (s: Nat)
    (no: Nat.leq from (s * d) = False) (hs: Succ s <= bLo)
    (ih: windowSum from to d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum from to d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  calc windowSum from to d (Succ c) s
    _ = windowSum from to d c (Succ s)
        := Eq.cong List.sum (List.filterSkip (x => from <= x && x <= to) (s * d) (List.map (b => b * d) (List.rangeFrom c (Succ s))) (Nat.betweenBelow from to (s * d) no))
    _ = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi)) := ih
    _ = d * Nat.span bLo (Nat.min (Succ s + c) (Succ bHi))                    := rewrite Nat.maxRight (Succ s) bLo hs
    _ = d * Nat.span bLo (Nat.min (s + Succ c) (Succ bHi))                    := rewrite Nat.addSucc s c
    _ = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi))        := rewrite Nat.maxRight s bLo (Nat.lessLe s bLo hs)

theorem windowIn (from: Nat) (to: Nat) (d: Nat) (bLo: Nat) (bHi: Nat) (c: Nat) (s: Nat)
    (yes: (from <= s * d && s * d <= to) = True) (hA: bLo <= s) (hB: s <= bHi)
    (ih: windowSum from to d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum from to d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  calc windowSum from to d (Succ c) s
    _ = s * d + windowSum from to d c (Succ s)
        := Eq.trans (Eq.cong List.sum (List.filterKeep (x => from <= x && x <= to) (s * d) (List.map (b => b * d) (List.rangeFrom c (Succ s))) yes))
             (List.sumCons (s * d) (List.filter (x => from <= x && x <= to) (List.map (b => b * d) (List.rangeFrom c (Succ s)))))
    _ = s * d + d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi)) := rewrite ih
    _ = s * d + d * Nat.span (Succ s) (Nat.min (Succ s + c) (Succ bHi))
        := rewrite Nat.maxLeft (Succ s) bLo (Nat.leTrans bLo s (Succ s) hA (Nat.leSucc s))
    _ = d * s + d * Nat.span (Succ s) (Nat.min (Succ s + c) (Succ bHi))               := rewrite Nat.mulComm s d
    _ = d * (s + Nat.span (Succ s) (Nat.min (Succ s + c) (Succ bHi)))                 := Eq.sym (Nat.mulDistribLeft d s (Nat.span (Succ s) (Nat.min (Succ s + c) (Succ bHi))))
    _ = d * Nat.span s (Nat.min (Succ s + c) (Succ bHi))
        := rewrite <- Nat.spanStep s (Nat.min (Succ s + c) (Succ bHi)) (Nat.leMin (Succ s) (Succ s + c) (Succ bHi) (Nat.leAddRight s c) hB)
    _ = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi))                := rewrite Nat.maxLeft s bLo hA, Nat.addSucc s c

theorem windowAbove (from: Nat) (to: Nat) (d: Nat) (bLo: Nat) (bHi: Nat) (c: Nat) (s: Nat)
    (low: from <= s * d) (no: Nat.leq (s * d) to = False) (hs: Succ bHi <= s)
    (ih: windowSum from to d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum from to d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  calc windowSum from to d (Succ c) s
    _ = windowSum from to d c (Succ s)
        := Eq.cong List.sum (List.filterSkip (x => from <= x && x <= to) (s * d) (List.map (b => b * d) (List.rangeFrom c (Succ s))) (Nat.betweenAbove from to (s * d) low no))
    _ = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi)) := ih
    _ = d * 0
        := rewrite Nat.spanEmpty (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))
             (calc Nat.min (Succ s + c) (Succ bHi)
               _ <= Succ bHi         := Nat.minLeRight (Succ s + c) (Succ bHi)
               _ <= s                := hs
               _ <= Succ s           := Nat.leSucc s
               _ <= Nat.max (Succ s) bLo := Nat.leMaxLeft (Succ s) bLo)
    _ = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi))
        := rewrite Nat.spanEmpty (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi))
             (calc Nat.min (s + Succ c) (Succ bHi)
               _ <= Succ bHi         := Nat.minLeRight (s + Succ c) (Succ bHi)
               _ <= s                := hs
               _ <= Nat.max s bLo    := Nat.leMaxLeft s bLo)

-- The heart of it: if `from <= b * d` exactly when `bLo <= b`, and `b * d <= to`
-- exactly when `b <= bHi`, then the ids `b * d` in `from..to` for `b` in a run of
-- `c` numbers from `s` are `d` times the sum of the run cut down to `bLo..bHi`.
theorem window (from: Nat) (to: Nat) (d: Nat) (bLo: Nat) (bHi: Nat)
    (yesA: (b: Nat) -> bLo <= b -> from <= b * d)
    (noA: (b: Nat) -> Nat.leq bLo b = False -> Nat.leq from (b * d) = False)
    (yesB: (b: Nat) -> b <= bHi -> b * d <= to)
    (noB: (b: Nat) -> Nat.leq b bHi = False -> Nat.leq (b * d) to = False):
    (c: Nat) -> (s: Nat) -> windowSum from to d c s = d * Nat.span (Nat.max s bLo) (Nat.min (s + c) (Succ bHi))
  | Zero,   s =>
    rewrite Nat.spanEmpty (Nat.max s bLo) (Nat.min (s + 0) (Succ bHi))
        (calc Nat.min (s + 0) (Succ bHi)
          _ <= s + 0         := Nat.minLeLeft (s + 0) (Succ bHi)
          _ = s              := Nat.addZero s
          _ <= Nat.max s bLo := Nat.leMaxLeft s bLo),
      Nat.mulZero d
  | Succ c, s =>
    match hA: Nat.leq bLo s, hB: Nat.leq s bHi with
      | True, True =>
        windowIn from to d bLo bHi c s (Nat.betweenYes from to (s * d) (yesA s hA) (yesB s hB)) hA hB
          (window from to d bLo bHi yesA noA yesB noB c (Succ s))
      | True, False =>
        windowAbove from to d bLo bHi c s (yesA s hA) (noB s hB) (Nat.leqFalse s bHi hB)
          (window from to d bLo bHi yesA noA yesB noB c (Succ s))
      | False, _ =>
        windowBelow from to d bLo bHi c s (noA s hA) (Nat.leqFalse bLo s hA)
          (window from to d bLo bHi yesA noA yesB noB c (Succ s))

-- The `if` at the end of `blocksAt`, after its `let`s.
theorem gaussPick (d: Nat) (from: Nat) (to: Nat):
    (if from <= to then d * ((from + to) * (to - from + 1) / 2) else 0) = d * Nat.span from (Succ to) :=
  match h: Nat.leq from to with
    | True  => Nat.gaussSpan d from to h
    | False => Eq.sym (Eq.trans (Eq.cong (t => d * t) (Nat.spanEmpty from (Succ to) (Nat.leqFalse from to h))) (Nat.mulZero d))

theorem blocksWindow (r: Range) (low: Nat): (p: Nat) -> 0 < p -> low <= p -> (m: Nat) ->
    blocksAt r low p m = windowSum r.from r.to m (p - low) low
  | Zero,   hp, hl, m      => Void.exfalso (Bool.falseNotTrue hp)
  | Succ p, hp, hl, Zero   => Eq.sym (windowZero r.from r.to (Succ p - low) low)
  | Succ p, hp, hl, Succ m =>
    calc blocksAt r low (Succ p) (Succ m)
      _ = Succ m * Nat.span (Nat.max low ((r.from + Succ m - 1) / Succ m)) (Succ (Nat.min p (r.to / Succ m)))
          := gaussPick (Succ m) (Nat.max low ((r.from + Succ m - 1) / Succ m)) (Nat.min p (r.to / Succ m))
      _ = Succ m * Nat.span (Nat.max low ((r.from + Succ m - 1) / Succ m)) (Nat.min (Succ p) (Succ (r.to / Succ m)))
          := rewrite Nat.minSucc p (r.to / Succ m)
      _ = Succ m * Nat.span (Nat.max low ((r.from + Succ m - 1) / Succ m)) (Nat.min (low + (Succ p - low)) (Succ (r.to / Succ m)))
          := rewrite Nat.addSubCancel low (Succ p) hl
      _ = windowSum r.from r.to (Succ m) (Succ p - low) low
          := Eq.sym (window r.from r.to (Succ m) ((r.from + Succ m - 1) / Succ m) (r.to / Succ m)
               (Nat.roundUpGe r.from m) (Nat.roundUpNo r.from m) (b h => Nat.mulLeOfLeDiv b r.to (Succ m) h) (Nat.roundDownNo r.to m)
               (Succ p - low) low)

-- (a) The arithmetic sum is the brute-force one.
theorem repeatedCorrect (r: Range) (k: Nat) (n: Nat): sumWithShape r { blockLength = k, copies = n } = repeatedSpec r k n :=
  Eq.trans (blocksWindow r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (Nat.powSuccPos 9 k) (Nat.powTenPredLe k) (multiplier k n))
    (Eq.sym (specWindow r k n))

-- Why `sumWithShape` is right (a'), for a block written twice:
-- `repeatedTwice` says `sumWithShape r` of the shape k by 2 is the sum the puzzle
-- describes, walking the ids of the range and keeping those whose digits are
-- some k-digit block written twice (any k from 1 on).
--
-- The outline: `repeatedSpec` walks blocks, so swap the order of the
-- two sums (`blocksAsIds`): for each id `x`, add `x` once for each k-digit
-- block that written twice makes `x`. That is one block when x's digits are
-- a k-digit block written twice, the block being x's first k digits
-- (`twiceValue`), and none otherwise, since a k-digit block written twice
-- has digits that are a k-digit block written twice (`twiceDigits`).

-- The ids from from to to that equal `y`, added up.
theorem sumIdsEq (from: Nat) (to: Nat) (y: Nat):
    List.sumBy (x => Nat.keepIf x (y == x)) (List.rangeFrom (to + 1 - from) from) = Nat.keepIf y (from <= y && y <= to) :=
  match t: Nat.leq from y, t2: Nat.leq y to with
    | True, True  => List.sumRangeEq y (to + 1 - from) from t (rangeIn from to y t t2)
    | True, False =>
      List.sumRangeEqNone y (to + 1 - from) from
        (x hx1 hx2 e => Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite <- e at rangeEnd from to x hx1 hx2)) t2))
    | False, _    =>
      List.sumRangeEqNone y (to + 1 - from) from
        (x hx1 hx2 e => Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite <- e at hx1)) t))

theorem twiceAppend (x: Nat) (k: Nat) (hq: writtenAs (Nat.digits x) k 2 = True):
    List.append (List.take k (Nat.digits x)) (List.take k (Nat.digits x)) = Nat.digits x :=
  Eq.trans (Eq.sym (Eq.cong (List.append (List.take k (Nat.digits x))) (List.appendNil (List.take k (Nat.digits x)))))
    (Decidable.toBoolSound (List.decEq (a b => Nat.decEq a b) (List.concat (List.replicate 2 (List.take k (Nat.digits x)))) (Nat.digits x)) hq)

theorem twiceBlockLength (x: Nat) (k: Nat) (hq: writtenAs (Nat.digits x) k 2 = True): List.length (List.take k (Nat.digits x)) = k :=
  match e: Nat.leq k (List.length (Nat.digits x)) with
    | True  => List.lengthTake k (Nat.digits x) e
    | False =>
      Void.exfalso (Nat.addSelfNotSelf (List.length (Nat.digits x)) (Nat.digitsNonEmpty x)
        (Eq.trans (Eq.sym (List.lengthAppend (Nat.digits x) (Nat.digits x)))
          (Eq.cong List.length
            (rewrite List.takeAll k (Nat.digits x) (Nat.lessLe (List.length (Nat.digits x)) k (Nat.leqFalse k (List.length (Nat.digits x)) e))
              at twiceAppend x k hq))))

theorem twiceHalf (x: Nat) (k: Nat) (hq: writtenAs (Nat.digits x) k 2 = True): k + k = List.length (Nat.digits x) :=
  calc k + k
    _ = List.length (List.take k (Nat.digits x)) + List.length (List.take k (Nat.digits x)) := rewrite twiceBlockLength x k hq
    _ = List.length (List.append (List.take k (Nat.digits x)) (List.take k (Nat.digits x)))
        := Eq.sym (List.lengthAppend (List.take k (Nat.digits x)) (List.take k (Nat.digits x)))
    _ = List.length (Nat.digits x) := rewrite twiceAppend x k hq

theorem twiceValue (x: Nat) (k: Nat) (hq: writtenAs (Nat.digits x) k 2 = True):
    writeTimes k (Nat.fromDigits (List.take k (Nat.digits x))) 2 = x :=
  calc writeTimes k (Nat.fromDigits (List.take k (Nat.digits x))) 2
    _ = Nat.fromDigits (List.take k (Nat.digits x)) * Nat.pow 10 (List.length (List.take k (Nat.digits x))) + Nat.fromDigits (List.take k (Nat.digits x))
        := rewrite twiceBlockLength x k hq
    _ = Nat.fromDigits (List.append (List.take k (Nat.digits x)) (List.take k (Nat.digits x)))
        := Eq.sym (Nat.fromDigitsAppend (List.take k (Nat.digits x)) (List.take k (Nat.digits x)))
    _ = Nat.fromDigits (Nat.digits x) := rewrite twiceAppend x k hq
    _ = x := Nat.fromDigitsDigits x

theorem twiceBelow (x: Nat) (k: Nat) (hq: writtenAs (Nat.digits x) k 2 = True):
    Nat.fromDigits (List.take k (Nat.digits x)) < Nat.pow 10 k :=
  calc Nat.fromDigits (List.take k (Nat.digits x))
    _ < Nat.pow 10 (List.length (List.take k (Nat.digits x)))
        := Nat.fromDigitsBound (List.take k (Nat.digits x)) (Nat.digitsTake k (Nat.digits x) (Nat.digitsDigits x))
    _ = Nat.pow 10 k := rewrite twiceBlockLength x k hq

theorem posOfHalves: (x: Nat) -> (k: Nat) -> k + k = List.length (Nat.digits x) -> 1 <= x
  | Zero,   k, e => Void.exfalso (Nat.doubleNotOne k e)
  | Succ x, k, e => rfl

theorem twiceAbove (x: Nat) (k: Nat) (hq: writtenAs (Nat.digits x) k 2 = True):
    Nat.pow 10 (k - 1) <= Nat.fromDigits (List.take k (Nat.digits x)) :=
  J (t q => Nat.pow 10 (t - 1) <= Nat.fromDigits (List.take k (Nat.digits x)))
    (Nat.fromDigitsHeadBound (List.take k (Nat.digits x))
      (Nat.leCongRight 1 (List.headOr 0 (Nat.digits x)) (List.headOr 0 (List.take k (Nat.digits x)))
        (Eq.sym (List.headTake 0 k (Nat.digits x) (Nat.posOfDouble k (List.length (Nat.digits x)) (twiceHalf x k hq) (Nat.digitsNonEmpty x))))
        (Nat.digitsHead x (posOfHalves x k (twiceHalf x k hq)))))
    (twiceBlockLength x k hq)

theorem twiceAtLeast (x: Nat) (k: Nat) (hq: writtenAs (Nat.digits x) k 2 = True): Nat.pow 10 k <= x :=
  calc Nat.pow 10 k
    _ = 1 * Nat.pow 10 k := Eq.sym (Nat.addZero (Nat.pow 10 k))
    _ <= Nat.fromDigits (List.take k (Nat.digits x)) * Nat.pow 10 k
        := Nat.leMulRight 1 (Nat.fromDigits (List.take k (Nat.digits x))) (Nat.pow 10 k)
             (Nat.leTrans 1 (Nat.pow 10 (k - 1)) (Nat.fromDigits (List.take k (Nat.digits x))) (Nat.powSuccPos 9 (k - 1)) (twiceAbove x k hq))
    _ <= writeTimes k (Nat.fromDigits (List.take k (Nat.digits x))) 2
        := Nat.leAddRight (Nat.fromDigits (List.take k (Nat.digits x)) * Nat.pow 10 k) (Nat.fromDigits (List.take k (Nat.digits x)))
    _ = x := twiceValue x k hq

-- The other way: a k-digit block written twice has digits that are a block written twice.
theorem writtenTwiceOf (p: List Nat) (k: Nat) (hk: p.length = k): writtenAs (List.append p p) k 2 = True :=
  Decidable.toBoolOf (List.decEq (a b => Nat.decEq a b) (List.concat (List.replicate 2 (List.take k (List.append p p)))) (List.append p p))
    (rewrite <- hk, List.takeAppend p p, List.appendNil p)

theorem twiceDigits (j: Nat) (b: Nat) (h1: Nat.pow 10 j <= b) (h2: b < Nat.pow 10 (Succ j)):
    writtenAs (Nat.digits (writeTimes (Succ j) b 2)) (Succ j) 2 = True :=
  rewrite <- (calc List.append (Nat.digits b) (Nat.digits b)
      _ = Nat.digits (b * Nat.pow 10 (List.length (Nat.digits b)) + Nat.fromDigits (Nat.digits b))
          := Eq.sym (Nat.digitsShift (Nat.digits b) b (Nat.leTrans 1 (Nat.pow 10 j) b (Nat.powSuccPos 9 j) h1) (Nat.digitsDigits b))
      _ = Nat.digits (b * Nat.pow 10 (List.length (Nat.digits b)) + b) := rewrite Nat.fromDigitsDigits b
      _ = Nat.digits (writeTimes (Succ j) b 2)                          := rewrite Nat.digitsLength j b h1 h2)
    in writtenTwiceOf (Nat.digits b) (Succ j) (Nat.digitsLength j b h1 h2)

theorem twiceInjective (k: Nat) (b: Nat) (v: Nat) (e: writeTimes k b 2 = writeTimes k v 2): b = v :=
  Nat.mulSuccCancel b v (Nat.pow 10 k * multiplier k 1)
    (calc b * Succ (Nat.pow 10 k * multiplier k 1)
      _ = b * multiplier k 2 := rewrite multiplierSucc k 1
      _ = writeTimes k b 2   := Eq.sym (writeTimesMul k b 2)
      _ = writeTimes k v 2   := e
      _ = v * multiplier k 2 := writeTimesMul k v 2
      _ = v * Succ (Nat.pow 10 k * multiplier k 1) := rewrite multiplierSucc k 1)

-- For one id `x` and block length k: the k-digit blocks written twice that
-- make `x` add up to `x` when x's digits are a k-digit block written twice,
-- and to 0 otherwise.
theorem twiceBlockCount (x: Nat): (k: Nat) -> 1 <= k ->
    List.sumBy (b => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
      = Nat.keepIf x (writtenAs (Nat.digits x) k 2)
  | Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ j, h =>
    match hq: writtenAs (Nat.digits x) (Succ j) 2 with
      | True =>
        List.sumRangeOne (b => writeTimes (Succ j) b 2 == x) (b => x) (Nat.fromDigits (List.take (Succ j) (Nat.digits x)))
          (Decidable.toBoolOf (Nat.decEq (writeTimes (Succ j) (Nat.fromDigits (List.take (Succ j) (Nat.digits x))) 2) x) (twiceValue x (Succ j) hq))
          (b hb => twiceInjective (Succ j) b (Nat.fromDigits (List.take (Succ j) (Nat.digits x)))
            (Eq.trans (Decidable.toBoolSound (Nat.decEq (writeTimes (Succ j) b 2) x) hb) (Eq.sym (twiceValue x (Succ j) hq))))
          (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
          (twiceAbove x (Succ j) hq)
          (calc Nat.fromDigits (List.take (Succ j) (Nat.digits x))
            _ < Nat.pow 10 (Succ j)                                  := twiceBelow x (Succ j) hq
            _ = Nat.pow 10 j + (Nat.pow 10 (Succ j) - Nat.pow 10 j) := Eq.sym (Nat.addSubCancel (Nat.pow 10 j) (Nat.pow 10 (Succ j)) (Nat.powTenPredLe (Succ j))))
      | False =>
        List.sumRangeNone (b => writeTimes (Succ j) b 2 == x) (b => x) (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
          (b h1 h2 => Decidable.toBoolOfNot (Nat.decEq (writeTimes (Succ j) b 2) x)
            (e => Bool.trueNotFalse (Eq.trans
              (Eq.sym (rewrite e at
                twiceDigits j b h1
                  (calc b
                    _ < Nat.pow 10 j + (Nat.pow 10 (Succ j) - Nat.pow 10 j) := h2
                    _ = Nat.pow 10 (Succ j) := Nat.addSubCancel (Nat.pow 10 j) (Nat.pow 10 (Succ j)) (Nat.powTenPredLe (Succ j)))))
              hq)))

-- One block length, as a sum over the ids of the range.
theorem blocksAsIds (r: Range) (k: Nat):
    repeatedSpec r k 2
      = List.sumBy (x => List.sumBy (b => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
          (List.rangeFrom (r.to + 1 - r.from) r.from) :=
  calc repeatedSpec r k 2
    -- filtering the block ids by the range is summing "the id if it is in the range"
    _ = List.sumBy (y => Nat.keepIf y (r.from <= y && y <= r.to)) (List.map (b => writeTimes k b 2) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
        := List.sumFilter (x => r.from <= x && x <= r.to) (List.map (b => writeTimes k b 2) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
    _ = List.sumBy (b => Nat.keepIf (writeTimes k b 2) (r.from <= writeTimes k b 2 && writeTimes k b 2 <= r.to)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
        := List.sumByMap (y => Nat.keepIf y (r.from <= y && y <= r.to)) (b => writeTimes k b 2) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
    -- and, for each block, "the id if it is in the range" is the sum over the range ids that equal it
    _ = List.sumBy (b => List.sumBy (x => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (r.to + 1 - r.from) r.from)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
        := List.sumByCong (b => Nat.keepIf (writeTimes k b 2) (r.from <= writeTimes k b 2 && writeTimes k b 2 <= r.to))
             (b => List.sumBy (x => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (r.to + 1 - r.from) r.from))
             (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
             (b => Eq.sym (sumIdsEq r.from r.to (writeTimes k b 2)))
    _ = List.sumBy (x => List.sumBy (b => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))) (List.rangeFrom (r.to + 1 - r.from) r.from)
        := List.sumBySwap (b x => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (r.to + 1 - r.from) r.from) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))

theorem twiceIds (r: Range) (k: Nat) (hk: 1 <= k):
    repeatedSpec r k 2 = List.sumBy (x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids :=
  Eq.trans (blocksAsIds r k)
    (List.sumByCong (x => List.sumBy (b => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
      (x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids (x => twiceBlockCount x k hk))

-- (a') A block written twice: the arithmetic sum is the sum of the ids in
-- the range whose digits are some k-digit block written twice.
theorem repeatedTwice (r: Range) (k: Nat) (hk: 1 <= k):
    sumWithShape r { blockLength = k, copies = 2 } = (r.ids |> .filter (x => writtenAs (Nat.digits x) k 2) |> .sum) :=
  calc sumWithShape r { blockLength = k, copies = 2 }
    _ = repeatedSpec r k 2 := repeatedCorrect r k 2
    _ = List.sumBy (x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids := twiceIds r k hk
    _ = (r.ids |> .filter (x => writtenAs (Nat.digits x) k 2) |> .sum) := Eq.sym (List.sumFilter (x => writtenAs (Nat.digits x) k 2) r.ids)

-- The shapes of a range, as a grid: summing over them is summing over every
-- block length up to the digits and every number of copies from 2, where
-- the shapes that don't fit count 0. (The grid is what Part1.sw and
-- Part2.sw work with.)
theorem betweenOne (n: Nat): List.between 1 n = List.rangeFrom n 1 := Eq.cong (t => List.rangeFrom t 1) (Nat.addSub n 1)

theorem betweenTwo: (n: Nat) -> List.between 2 n = List.rangeFrom (n - 1) 2
  | Zero   => rfl
  | Succ n => Eq.cong (t => List.rangeFrom t 2) (Nat.addSub n 1)

theorem shapesSum [auto add: Add c] (r: Range) (f: RepetitionTemplate -> c):
    List.sumBy f (shapes r)
      = List.sumBy (k => List.sumBy (n => if Nat.leq (k * n) (List.length (Nat.digits r.to)) then f { blockLength = k, copies = n } else Add.zero)
          (List.rangeFrom (List.length (Nat.digits r.to) - 1) 2)) (List.rangeFrom (List.length (Nat.digits r.to)) 1) :=
  let size := List.length (Nat.digits r.to)
  let fits: Nat -> Nat -> Bool := k n => k * n <= size
  let withCopies: Nat -> List RepetitionTemplate := k => List.map (n => { blockLength = k, copies = n }) (List.filter (fits k) (List.between 2 size))
  calc List.sumBy f (shapes r)
    _ = List.sumBy (k => List.sumBy f (withCopies k)) (List.between 1 size) := List.sumByFlatMap f withCopies (List.between 1 size)
    _ = List.sumBy (k => List.sumBy (n => if fits k n then f { blockLength = k, copies = n } else Add.zero) (List.between 2 size)) (List.between 1 size)
        := List.sumByCong (k => List.sumBy f (withCopies k)) (k => List.sumBy (n => if fits k n then f { blockLength = k, copies = n } else Add.zero) (List.between 2 size))
             (List.between 1 size)
             (k => Eq.trans (List.sumByMap f (n => { blockLength = k, copies = n }) (List.filter (fits k) (List.between 2 size)))
                     (List.sumByFilter (n => f { blockLength = k, copies = n }) (fits k) (List.between 2 size)))
    -- (`<=` in a program is `Nat.leq` under `Decidable.toBool`.)
    _ = List.sumBy (k => List.sumBy (n => if Nat.leq (k * n) size then f { blockLength = k, copies = n } else Add.zero) (List.between 2 size)) (List.between 1 size)
        := List.sumByCong (k => List.sumBy (n => if fits k n then f { blockLength = k, copies = n } else Add.zero) (List.between 2 size))
             (k => List.sumBy (n => if Nat.leq (k * n) size then f { blockLength = k, copies = n } else Add.zero) (List.between 2 size))
             (List.between 1 size)
             (k => List.sumByCong (n => if fits k n then f { blockLength = k, copies = n } else Add.zero)
                     (n => if Nat.leq (k * n) size then f { blockLength = k, copies = n } else Add.zero) (List.between 2 size)
                     (n => Eq.cong (b => if b then f { blockLength = k, copies = n } else Add.zero) (Bool.decTrueToBool (Nat.leq (k * n) size))))
    _ = List.sumBy (k => List.sumBy (n => if Nat.leq (k * n) size then f { blockLength = k, copies = n } else Add.zero) (List.rangeFrom (size - 1) 2)) (List.rangeFrom size 1)
        := rewrite betweenOne size, betweenTwo size
