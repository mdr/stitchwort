-- Code shared between days.

namespace Aoc.Common

-- A range of ids, both ends included: "3-5" is `{ lo = 3, hi = 5 }`.
type Range = { lo: Nat, hi: Nat }

def Range.parse (t: Text): Maybe Range :=
  match (t.split '-').map Text.toNat with
    | [Just lo, Just hi] => Just { lo, hi }
    | _                  => Nothing

test "parse" := Range.parse "3-5" == Just { lo = 3, hi = 5 }
test "parse junk" := Range.parse "4-x" == Nothing

-- The sum of the ids in the range that are a k-digit block written n times.
-- m is the multiplier: 12 written 3 times is 12 * 10101, and 10101 is
-- 1 + 10^2 + 10^4.
def Range.repeated (r: Range) (k: Nat) (n: Nat): Nat :=
  let m := List.range n |> .sumBy (\i => Nat.pow 10 (k * i))
  if m != 0 then
    let lo := Nat.max (Nat.pow 10 (k - 1)) ((r.lo + m - 1) / m)
    let hi := Nat.min (Nat.pow 10 k - 1) (r.hi / m)
    if lo <= hi then m * ((lo + hi) * (hi - lo + 1) / 2) else 0
  else 0

test "12 written 3 times" := Range.repeated { lo = 0, hi = 1000000 } 2 3 == 10101 * ((10 + 99) * 90 / 2)

-- Why `Range.repeated` is right (a): `Range.repeated r k n` equals
-- `Range.repeatedSpec r k n`, the brute-force sum below, for every range, block
-- length and repeat count.
--
-- The outline: writing a block `b` n times gives `b * m`
-- (`writeTimesMul`); `lo <= b * m <= hi` exactly when `b` is between
-- `lo / m` rounded up and `hi / m` rounded down (`Nat.roundUpLe` and friends);
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
def Range.repeatedSpec (r: Range) (k: Nat) (n: Nat): Nat :=
  List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))
    |> .map (\b => writeTimes k b n)
    |> .filter (\x => r.lo <= x && x <= r.hi)
    |> .sum

-- `Range.repeated` with its parts as parameters: the multiplier `m`, the
-- smallest block `low` and the first number too long to be a block `p`.
def multiplier (k: Nat) (n: Nat): Nat := List.range n |> .sumBy (\i => Nat.pow 10 (k * i))

def blocksAt (r: Range) (low: Nat) (p: Nat) (m: Nat): Nat :=
  if m != 0 then
    let lo := Nat.max low ((r.lo + m - 1) / m)
    let hi := Nat.min (p - 1) (r.hi / m)
    if lo <= hi then m * ((lo + hi) * (hi - lo + 1) / 2) else 0
  else 0

theorem repeatedAt (r: Range) (k: Nat) (n: Nat): Range.repeated r k n = blocksAt r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (multiplier k n) := rfl

-- The multiplier: writing `b` n times is `b * multiplier k n`.
theorem multiplierSucc (k: Nat) (n: Nat): multiplier k (Succ n) = 1 + Nat.pow 10 k * multiplier k n :=
  Eq.trans (List.sumByCons (\i => Nat.pow 10 (k * i)) 0 (List.rangeFrom n 1))
    (Eq.trans (Eq.cong (\t => Nat.pow 10 t + List.sumBy (\i => Nat.pow 10 (k * i)) (List.rangeFrom n 1)) (Nat.mulZero k))
      (Eq.cong (\t => 1 + t)
        (Eq.trans (List.sumByRangeShift (\i => Nat.pow 10 (k * i)) n 0)
          (Eq.trans (List.sumByCongr (\i => Nat.pow 10 (k * Succ i)) (\i => Nat.pow 10 k * Nat.pow 10 (k * i))
              (\i => Eq.trans (Eq.cong (\t => Nat.pow 10 t) (Nat.mulSucc k i)) (Nat.powAdd 10 k (k * i))) (List.range n))
            (List.sumByMulLeft (Nat.pow 10 k) (\i => Nat.pow 10 (k * i)) (List.range n))))))

theorem writeTimesMul (k: Nat) (b: Nat): (n: Nat) -> writeTimes k b n = b * multiplier k n
  | Zero   => Eq.sym (Nat.mulZero b)
  | Succ n =>
    Eq.trans (Eq.cong (\t => t * Nat.pow 10 k + b) (writeTimesMul k b n))
      (Eq.trans (Eq.cong (\t => t + b) (Nat.mulAssoc b (multiplier k n) (Nat.pow 10 k)))
        (Eq.trans (Eq.cong (\t => b * t + b) (Nat.mulComm (multiplier k n) (Nat.pow 10 k)))
          (Eq.trans (Nat.addComm (b * (Nat.pow 10 k * multiplier k n)) b)
            (Eq.trans (Eq.cong (\t => t + b * (Nat.pow 10 k * multiplier k n)) (Eq.sym (Nat.mulOne b)))
              (Eq.trans (Eq.sym (Nat.mulDistribLeft b 1 (Nat.pow 10 k * multiplier k n)))
                (Eq.cong (\t => b * t) (Eq.sym (multiplierSucc k n))))))))

-- The ids `b * d` for `b` from `s` to `s + c - 1` that lie in `lo..hi`, added up.
def windowSum (lo: Nat) (hi: Nat) (d: Nat) (c: Nat) (s: Nat): Nat :=
  List.sum (List.filter (\x => lo <= x && x <= hi) (List.map (\b => b * d) (List.rangeFrom c s)))

theorem specWindow (r: Range) (k: Nat) (n: Nat):
    Range.repeatedSpec r k n = windowSum r.lo r.hi (multiplier k n) (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)) :=
  Eq.cong (\xs => List.sum (List.filter (\x => r.lo <= x && x <= r.hi) xs))
    (List.mapCongr (\b => writeTimes k b n) (\b => b * multiplier k n) (\b => writeTimesMul k b n)
      (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))

-- With a multiplier of 0 every id is 0.
theorem windowZero (lo: Nat) (hi: Nat): (c: Nat) -> (s: Nat) -> windowSum lo hi 0 c s = 0
  | Zero,   s => rfl
  | Succ c, s =>
    Bool.inspect (lo <= s * 0 && s * 0 <= hi) (\u => windowSum lo hi 0 (Succ c) s = 0)
      (\h => Eq.trans (Eq.cong List.sum (List.filterKeep (\x => lo <= x && x <= hi) (s * 0) (List.map (\b => b * 0) (List.rangeFrom c (Succ s))) h))
        (Eq.trans (List.sumCons (s * 0) (List.filter (\x => lo <= x && x <= hi) (List.map (\b => b * 0) (List.rangeFrom c (Succ s)))))
          (Eq.trans (Eq.cong (\t => t + windowSum lo hi 0 c (Succ s)) (Nat.mulZero s)) (windowZero lo hi c (Succ s)))))
      (\h => Eq.trans (Eq.cong List.sum (List.filterSkip (\x => lo <= x && x <= hi) (s * 0) (List.map (\b => b * 0) (List.rangeFrom c (Succ s))) h))
        (windowZero lo hi c (Succ s)))

-- One step of `window`, for each place `s` can be: below `bLo`, in `bLo..bHi`, above `bHi`.
theorem windowBelow (lo: Nat) (hi: Nat) (d: Nat) (bLo: Nat) (bHi: Nat) (c: Nat) (s: Nat)
    (no: Nat.leq lo (s * d) = False) (hs: Succ s <= bLo)
    (ih: windowSum lo hi d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum lo hi d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  Eq.trans (Eq.cong List.sum (List.filterSkip (\x => lo <= x && x <= hi) (s * d) (List.map (\b => b * d) (List.rangeFrom c (Succ s))) (Nat.betweenBelow lo hi (s * d) no)))
    (Eq.trans ih
      (Eq.trans (Eq.cong (\t => d * Nat.span t (Nat.min (Succ s + c) (Succ bHi))) (Nat.maxRight (Succ s) bLo hs))
        (Eq.sym (Eq.trans (Eq.cong (\t => d * Nat.span t (Nat.min (s + Succ c) (Succ bHi))) (Nat.maxRight s bLo (Nat.lessLe s bLo hs)))
          (Eq.cong (\t => d * Nat.span bLo (Nat.min t (Succ bHi))) (Nat.addSucc s c))))))

theorem windowIn (lo: Nat) (hi: Nat) (d: Nat) (bLo: Nat) (bHi: Nat) (c: Nat) (s: Nat)
    (yes: (lo <= s * d && s * d <= hi) = True) (hA: bLo <= s) (hB: s <= bHi)
    (ih: windowSum lo hi d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum lo hi d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  Eq.trans (Eq.cong List.sum (List.filterKeep (\x => lo <= x && x <= hi) (s * d) (List.map (\b => b * d) (List.rangeFrom c (Succ s))) yes))
    (Eq.trans (List.sumCons (s * d) (List.filter (\x => lo <= x && x <= hi) (List.map (\b => b * d) (List.rangeFrom c (Succ s)))))
      (Eq.trans (Eq.cong (\t => s * d + t) ih)
        (Eq.trans (Eq.cong (\t => s * d + d * Nat.span t (Nat.min (Succ s + c) (Succ bHi))) (Nat.maxLeft (Succ s) bLo (Nat.leTrans bLo s (Succ s) hA (Nat.leSucc s))))
          (Eq.trans (Eq.cong (\t => t + d * Nat.span (Succ s) (Nat.min (Succ s + c) (Succ bHi))) (Nat.mulComm s d))
            (Eq.sym
              (Eq.trans (Eq.cong (\t => d * Nat.span t (Nat.min (s + Succ c) (Succ bHi))) (Nat.maxLeft s bLo hA))
                (Eq.trans (Eq.cong (\t => d * Nat.span s (Nat.min t (Succ bHi))) (Nat.addSucc s c))
                  (Eq.trans (Eq.cong (\t => d * t) (Nat.spanStep s (Nat.min (Succ s + c) (Succ bHi)) (Nat.leMin (Succ s) (Succ s + c) (Succ bHi) (Nat.leAddRight s c) hB)))
                    (Nat.mulDistribLeft d s (Nat.span (Succ s) (Nat.min (Succ s + c) (Succ bHi))))))))))))

theorem windowAbove (lo: Nat) (hi: Nat) (d: Nat) (bLo: Nat) (bHi: Nat) (c: Nat) (s: Nat)
    (low: lo <= s * d) (no: Nat.leq (s * d) hi = False) (hs: Succ bHi <= s)
    (ih: windowSum lo hi d c (Succ s) = d * Nat.span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))):
    windowSum lo hi d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  Eq.trans (Eq.cong List.sum (List.filterSkip (\x => lo <= x && x <= hi) (s * d) (List.map (\b => b * d) (List.rangeFrom c (Succ s))) (Nat.betweenAbove lo hi (s * d) low no)))
    (Eq.trans ih
      (Eq.trans (Eq.cong (\t => d * t)
          (Nat.spanEmpty (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))
            (Nat.leTrans (Nat.min (Succ s + c) (Succ bHi)) (Succ s) (Nat.max (Succ s) bLo)
              (Nat.leTrans (Nat.min (Succ s + c) (Succ bHi)) (Succ bHi) (Succ s) (Nat.minLeRight (Succ s + c) (Succ bHi)) (Nat.leTrans (Succ bHi) s (Succ s) hs (Nat.leSucc s)))
              (Nat.leMaxLeft (Succ s) bLo))))
        (Eq.trans (Nat.mulZero d)
          (Eq.sym (Eq.trans (Eq.cong (\t => d * t)
              (Nat.spanEmpty (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi))
                (Nat.leTrans (Nat.min (s + Succ c) (Succ bHi)) s (Nat.max s bLo)
                  (Nat.leTrans (Nat.min (s + Succ c) (Succ bHi)) (Succ bHi) s (Nat.minLeRight (s + Succ c) (Succ bHi)) hs)
                  (Nat.leMaxLeft s bLo))))
            (Nat.mulZero d))))))

-- The heart of it: if `lo <= b * d` exactly when `bLo <= b`, and `b * d <= hi`
-- exactly when `b <= bHi`, then the ids `b * d` in `lo..hi` for `b` in a run of
-- `c` numbers from `s` are `d` times the sum of the run cut down to `bLo..bHi`.
theorem window (lo: Nat) (hi: Nat) (d: Nat) (bLo: Nat) (bHi: Nat)
    (yesA: (b: Nat) -> bLo <= b -> lo <= b * d)
    (noA: (b: Nat) -> Nat.leq bLo b = False -> Nat.leq lo (b * d) = False)
    (yesB: (b: Nat) -> b <= bHi -> b * d <= hi)
    (noB: (b: Nat) -> Nat.leq b bHi = False -> Nat.leq (b * d) hi = False):
    (c: Nat) -> (s: Nat) -> windowSum lo hi d c s = d * Nat.span (Nat.max s bLo) (Nat.min (s + c) (Succ bHi))
  | Zero,   s =>
    Eq.sym (Eq.trans (Eq.cong (\t => d * t)
        (Nat.spanEmpty (Nat.max s bLo) (Nat.min (s + 0) (Succ bHi))
          (Nat.leTrans (Nat.min (s + 0) (Succ bHi)) s (Nat.max s bLo)
            (Nat.leCongRight (Nat.min (s + 0) (Succ bHi)) (s + 0) s (Nat.addZero s) (Nat.minLeLeft (s + 0) (Succ bHi)))
            (Nat.leMaxLeft s bLo))))
      (Nat.mulZero d))
  | Succ c, s =>
    Bool.inspect (Nat.leq bLo s) (\u => windowSum lo hi d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)))
      (\hA => Bool.inspect (Nat.leq s bHi) (\u => windowSum lo hi d (Succ c) s = d * Nat.span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)))
        (\hB => windowIn lo hi d bLo bHi c s (Nat.betweenYes lo hi (s * d) (yesA s hA) (yesB s hB)) hA hB (window lo hi d bLo bHi yesA noA yesB noB c (Succ s)))
        (\nB => windowAbove lo hi d bLo bHi c s (yesA s hA) (noB s nB) (Nat.leqFalse s bHi nB) (window lo hi d bLo bHi yesA noA yesB noB c (Succ s))))
      (\nA => windowBelow lo hi d bLo bHi c s (noA s nA) (Nat.leqFalse bLo s nA) (window lo hi d bLo bHi yesA noA yesB noB c (Succ s)))

-- The `if` at the end of `blocksAt`, after its `let`s. A proof by cases
-- replaces its condition `Nat.leq lo hi` by a variable `c`; `if IsTrue c`
-- decides with `Bool.decTrue c`, as `if lo <= hi` does (`if c = True` would
-- use `Bool.decEq`, a different term).
def IsTrue (c: Bool): Prop := c = True

def decIsTrue (c: Bool): Decidable (IsTrue c) := Bool.decTrue c

theorem gaussPick (d: Nat) (lo: Nat) (hi: Nat):
    (if lo <= hi then d * ((lo + hi) * (hi - lo + 1) / 2) else 0) = d * Nat.span lo (Succ hi) :=
  Bool.inspect (Nat.leq lo hi)
    (\c => (if IsTrue c then d * ((lo + hi) * (hi - lo + 1) / 2) else 0) = d * Nat.span lo (Succ hi))
    (\h => Nat.gaussSpan d lo hi h)
    (\h => Eq.sym (Eq.trans (Eq.cong (\t => d * t) (Nat.spanEmpty lo (Succ hi) (Nat.leqFalse lo hi h))) (Nat.mulZero d)))

theorem blocksWindow (r: Range) (low: Nat): (p: Nat) -> 0 < p -> low <= p -> (m: Nat) ->
    blocksAt r low p m = windowSum r.lo r.hi m (p - low) low
  | Zero,   hp, hl, m      => Void.exfalso (Bool.falseNotTrue hp)
  | Succ p, hp, hl, Zero   => Eq.sym (windowZero r.lo r.hi (Succ p - low) low)
  | Succ p, hp, hl, Succ m =>
    Eq.trans (gaussPick (Succ m) (Nat.max low ((r.lo + Succ m - 1) / Succ m)) (Nat.min p (r.hi / Succ m)))
      (Eq.sym
        (Eq.trans
          (window r.lo r.hi (Succ m) ((r.lo + Succ m - 1) / Succ m) (r.hi / Succ m)
            (Nat.roundUpGe r.lo m) (Nat.roundUpNo r.lo m) (\b h => Nat.mulLeOfLeDiv b r.hi (Succ m) h) (Nat.roundDownNo r.hi m)
            (Succ p - low) low)
          (Eq.trans (Eq.cong (\t => Succ m * Nat.span (Nat.max low ((r.lo + Succ m - 1) / Succ m)) (Nat.min t (Succ (r.hi / Succ m)))) (Nat.addSubCancel low (Succ p) hl))
            (Eq.cong (\t => Succ m * Nat.span (Nat.max low ((r.lo + Succ m - 1) / Succ m)) t) (Nat.minSucc p (r.hi / Succ m))))))

-- (a) The arithmetic sum is the brute-force one.
theorem Range.repeatedCorrect (r: Range) (k: Nat) (n: Nat): Range.repeated r k n = Range.repeatedSpec r k n :=
  Eq.trans (blocksWindow r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (Nat.powSuccPos 9 k) (Nat.powTenPredLe k) (multiplier k n))
    (Eq.sym (specWindow r k n))

-- The invalid ids in the range under a weighting of the repeat counts: every
-- block size k and repeat count n that fit in the digits of `hi` (n is at
-- most 10, the most the weights cover).
def Range.invalid (w: Nat -> Int) (r: Range): Int :=
  let size := (Nat.digits r.hi).length
  -- `size` is a parameter (not the `let`'s, which `terms` would know is
  -- the digit count) so the lemmas about `terms` state them for any size.
  def terms (size: Nat) (k: Nat): List Int :=
    List.rangeFrom 9 2
      |> .filter (\n => k * n <= size)
      |> .map (\n => w n * (Range.repeated r k n).toInt)
  List.rangeFrom size 1
    |> .concatMap (terms size)
    |> .sumInt

def Range.contains (r: Range) (id: Nat): Bool := r.lo <= id && id <= r.hi

test "contains" := (Range.contains { lo = 3, hi = 5 } 3, Range.contains { lo = 3, hi = 5 } 5, Range.contains { lo = 3, hi = 5 } 6) == (True, True, False)

def Range.size (r: Range): Nat := r.hi + 1 - r.lo

test "size" := Range.size { lo = 3, hi = 5 } == 3
