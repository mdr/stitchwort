-- Advent of Code 2025, day 2: product ids. An id is invalid when its decimal
-- digits are some block written twice (part 1) or two or more times (part 2).
-- Sum the invalid ids that lie in any of the given ranges.
--
--   $ cd aoc && stitchwort run Aoc.Day02.main < inputs/day02.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- Rather than test every id, add up the invalid ones arithmetically. The
-- ids made of a k-digit block written n times are base * m for the k-digit
-- bases, where m = 1 + 10^k + 10^2k + ... (12 written 3 times is
-- 12 * 10101). Those bases form an interval, so their sum is an arithmetic
-- series. Part 2 must not count 111111 three times (1 six times, 11 three
-- times, 111 twice): by inclusion-exclusion over n, the ids with some proper
-- period are the sum over n of -mu(n) times the ids with n blocks, where mu
-- is the Moebius function. The weights -mu(n) are computed (`plus`, `minus`),
-- so ids of any length work.

namespace Aoc.Day02
import Aoc.Common (Range, rangeIn, rangeEnd)
import Std (Eq)

def main(): {IO} () :=
  let ranges := parseRanges (IO.readAll())
  IO.print "Part 1: ${solvePart1 ranges}"
  IO.print "Part 2: ${solvePart2 ranges}"

def solvePart1 (ranges: List Range): Nat := ranges |> .sumBy (weighted twice)

def solvePart2 (ranges: List Range): Nat := ranges |> .sumBy invalid

-- One range: the ids counted with a plus, less those counted with a minus.
def invalid (r: Range): Nat := weighted plus r - weighted minus r

-- The ids in the range under weights `w` for the repeat counts: for every
-- block length k and repeat count n whose ids fit in the digits of `to`, the
-- ids that are a k-digit block written n times, times `w n`.
def weighted (w: Nat -> Nat) (r: Range): Nat :=
  let size := (Nat.digits r.to).length
  List.rangeFrom size 1 |> .sumBy (\k =>
    List.rangeFrom (size - 1) 2 |> .sumBy (\n => if Nat.leq (k * n) size then w n * repeated r k n else 0))

-- The weights. Repeat count n has weight `plus n - minus n` (minus the
-- Moebius function), chosen so that for every K >= 2 the weights of the
-- divisors of K from 2 on add up to 1:
--
--   plus K  = 1 + (minus d, added up over the divisors d of K with 2 <= d < K)
--   minus K =     (plus d,  added up over the same divisors)
--
-- The two parts are kept apart so that everything is a natural number.
-- `weightFuel fuel True n` is `plus n` and `weightFuel fuel False n` is
-- `minus n`; the fuel makes the recursion structural, and n + 1 is enough.
def plus (n: Nat): Nat := weightFuel (Succ n) True n

def minus (n: Nat): Nat := weightFuel (Succ n) False n

def weightFuel: Nat -> Bool -> Nat -> Nat
  | Zero,   s,     n => 0
  | Succ f, True,  n => 1 + divisorWeights (\d => weightFuel f False d) n (n - 2)
  | Succ f, False, n => divisorWeights (\d => weightFuel f True d) n (n - 2)

-- The weights w of the divisors of m among 2, 3, ..., c + 1, added up. (An
-- `if` rather than `Nat.keepIf`, so that only the divisors' weights are computed.)
def divisorWeights (w: Nat -> Nat) (m: Nat) (c: Nat): Nat :=
  List.rangeFrom c 2 |> .sumBy (\d => if Nat.divides d m then w d else 0)

test "weights" := List.map (\n => (plus n).toInt - (minus n).toInt) (List.rangeFrom 11 2) == [1, 1, 0, 1, -1, 1, 0, 0, -1, 1, 0]

-- Part 1 only wants a block written exactly twice.
def twice (n: Nat): Nat := if n == 2 then 1 else 0

test "single range" := weighted twice (range 11 22) == 33
test "no double counting" := invalid (range 111110 111112) == 111111
test "period three" := invalid (range 998 1012) == 999 + 1010
test "empty overlap" := invalid (range 12 21) == 0


-- The sum of the ids in the range that are a k-digit block written n times.
-- m is the multiplier: 12 written 3 times is 12 * 10101, and 10101 is
-- 1 + 10^2 + 10^4.
def repeated (r: Range) (k: Nat) (n: Nat): Nat :=
  let m := List.range n |> .sumBy (\i => Nat.pow 10 (k * i))
  if m != 0 then
    let from := Nat.max (Nat.pow 10 (k - 1)) ((r.from + m - 1) / m)
    let to := Nat.min (Nat.pow 10 k - 1) (r.to / m)
    if from <= to then m * ((from + to) * (to - from + 1) / 2) else 0
  else 0

test "12 written 3 times" := repeated { from = 0, to = 1000000 } 2 3 == 10101 * ((10 + 99) * 90 / 2)

-- Why `repeated` is right (a): `repeated r k n` equals
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
    |> .map (\b => writeTimes k b n)
    |> .filter (\x => r.from <= x && x <= r.to)
    |> .sum

-- `repeated` with its parts as parameters: the multiplier `m`, the
-- smallest block `low` and the first number too long to be a block `p`.
def multiplier (k: Nat) (n: Nat): Nat := List.range n |> .sumBy (\i => Nat.pow 10 (k * i))

def blocksAt (r: Range) (low: Nat) (p: Nat) (m: Nat): Nat :=
  if m != 0 then
    let from := Nat.max low ((r.from + m - 1) / m)
    let to := Nat.min (p - 1) (r.to / m)
    if from <= to then m * ((from + to) * (to - from + 1) / 2) else 0
  else 0

theorem repeatedAt (r: Range) (k: Nat) (n: Nat): repeated r k n = blocksAt r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (multiplier k n) := rfl

-- The multiplier: writing `b` n times is `b * multiplier k n`.
theorem multiplierSucc (k: Nat) (n: Nat): multiplier k (Succ n) = 1 + Nat.pow 10 k * multiplier k n :=
  calc multiplier k (Succ n)
    _ = Nat.pow 10 (k * 0) + List.sumBy (\i => Nat.pow 10 (k * i)) (List.rangeFrom n 1)
        := List.sumByCons (\i => Nat.pow 10 (k * i)) 0 (List.rangeFrom n 1)
    _ = 1 + List.sumBy (\i => Nat.pow 10 (k * i)) (List.rangeFrom n 1) := rewrite Nat.mulZero k
    _ = 1 + List.sumBy (\i => Nat.pow 10 (k * Succ i)) (List.range n)  := rewrite List.sumByRangeShift (\i => Nat.pow 10 (k * i)) n 0
    _ = 1 + List.sumBy (\i => Nat.pow 10 k * Nat.pow 10 (k * i)) (List.range n)
        := rewrite List.sumByCongr (\i => Nat.pow 10 (k * Succ i)) (\i => Nat.pow 10 k * Nat.pow 10 (k * i))
             (\i => Eq.trans (Eq.cong (\t => Nat.pow 10 t) (Nat.mulSucc k i)) (Nat.powAdd 10 k (k * i))) (List.range n)
    _ = 1 + Nat.pow 10 k * multiplier k n := rewrite List.sumByMulLeft (Nat.pow 10 k) (\i => Nat.pow 10 (k * i)) (List.range n)

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
  List.sum (List.filter (\x => from <= x && x <= to) (List.map (\b => b * d) (List.rangeFrom c s)))

theorem specWindow (r: Range) (k: Nat) (n: Nat):
    repeatedSpec r k n = windowSum r.from r.to (multiplier k n) (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)) :=
  rewrite List.mapCongr (\b => writeTimes k b n) (\b => b * multiplier k n) (\b => writeTimesMul k b n)
    (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))

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
        := Eq.cong List.sum (List.filterSkip (\x => from <= x && x <= to) (s * d) (List.map (\b => b * d) (List.rangeFrom c (Succ s))) (Nat.betweenBelow from to (s * d) no))
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
        := Eq.trans (Eq.cong List.sum (List.filterKeep (\x => from <= x && x <= to) (s * d) (List.map (\b => b * d) (List.rangeFrom c (Succ s))) yes))
             (List.sumCons (s * d) (List.filter (\x => from <= x && x <= to) (List.map (\b => b * d) (List.rangeFrom c (Succ s)))))
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
        := Eq.cong List.sum (List.filterSkip (\x => from <= x && x <= to) (s * d) (List.map (\b => b * d) (List.rangeFrom c (Succ s))) (Nat.betweenAbove from to (s * d) low no))
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
    | False => Eq.sym (Eq.trans (Eq.cong (\t => d * t) (Nat.spanEmpty from (Succ to) (Nat.leqFalse from to h))) (Nat.mulZero d))

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
               (Nat.roundUpGe r.from m) (Nat.roundUpNo r.from m) (\b h => Nat.mulLeOfLeDiv b r.to (Succ m) h) (Nat.roundDownNo r.to m)
               (Succ p - low) low)

-- (a) The arithmetic sum is the brute-force one.
theorem repeatedCorrect (r: Range) (k: Nat) (n: Nat): repeated r k n = repeatedSpec r k n :=
  Eq.trans (blocksWindow r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (Nat.powSuccPos 9 k) (Nat.powTenPredLe k) (multiplier k n))
    (Eq.sym (specWindow r k n))

-- Why `repeated` is right (a'), for a block written twice:
-- `repeatedTwice` says `repeated r k 2` is the sum the puzzle
-- describes, walking the ids of the range and keeping those whose digits are
-- some k-digit block written twice (any k from 1 on).
--
-- The outline: `repeatedSpec` walks blocks, so swap the order of the
-- two sums (`blocksAsIds`): for each id `x`, add `x` once for each k-digit
-- block that written twice makes `x`. That is one block when x's digits are
-- a k-digit block written twice, the block being x's first k digits
-- (`twiceValue`), and none otherwise, since a k-digit block written twice
-- has digits that are a k-digit block written twice (`twiceDigits`).

-- The digits are some block of k digits written n times.
def writtenAs (ds: List Nat) (k: Nat) (n: Nat): Bool := List.concat (List.replicate n (List.take k ds)) == ds

test "written as" := (writtenAs [1, 2, 1, 2] 2 2, writtenAs [1, 2, 1, 2] 1 4, writtenAs [1, 1, 1] 1 3) == (True, False, True)

-- The ids from from to to that equal `y`, added up.
theorem sumIdsEq (from: Nat) (to: Nat) (y: Nat):
    List.sumBy (\x => Nat.keepIf x (y == x)) (List.rangeFrom (to + 1 - from) from) = Nat.keepIf y (from <= y && y <= to) :=
  match t: Nat.leq from y, t2: Nat.leq y to with
    | True, True  => List.sumRangeEq y (to + 1 - from) from t (rangeIn from to y t t2)
    | True, False =>
      List.sumRangeEqNone y (to + 1 - from) from
        (\x hx1 hx2 e => Bool.trueNotFalse (Eq.trans (Eq.sym (J (\z q => Nat.leq z to = True) (rangeEnd from to x hx1 hx2) (Eq.sym e))) t2))
    | False, _    =>
      List.sumRangeEqNone y (to + 1 - from) from
        (\x hx1 hx2 e => Bool.trueNotFalse (Eq.trans (Eq.sym (J (\z q => Nat.leq from z = True) hx1 (Eq.sym e))) t))

theorem twiceAppend (x: Nat) (k: Nat) (hq: writtenAs (Nat.digits x) k 2 = True):
    List.append (List.take k (Nat.digits x)) (List.take k (Nat.digits x)) = Nat.digits x :=
  Eq.trans (Eq.sym (Eq.cong (List.append (List.take k (Nat.digits x))) (List.appendNil (List.take k (Nat.digits x)))))
    (Decidable.toBoolSound (List.decEq (\a b => Nat.decEq a b) (List.concat (List.replicate 2 (List.take k (Nat.digits x)))) (Nat.digits x)) hq)

theorem twiceBlockLength (x: Nat) (k: Nat) (hq: writtenAs (Nat.digits x) k 2 = True): List.length (List.take k (Nat.digits x)) = k :=
  match e: Nat.leq k (List.length (Nat.digits x)) with
    | True  => List.lengthTake k (Nat.digits x) e
    | False =>
      Void.exfalso (Nat.addSelfNotSelf (List.length (Nat.digits x)) (Nat.digitsNonEmpty x)
        (Eq.trans (Eq.sym (List.lengthAppend (Nat.digits x) (Nat.digits x)))
          (Eq.cong List.length
            (J (\l q => List.append l l = Nat.digits x) (twiceAppend x k hq)
              (List.takeAll k (Nat.digits x) (Nat.lessLe (List.length (Nat.digits x)) k (Nat.leqFalse k (List.length (Nat.digits x)) e)))))))

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
  J (\t q => Nat.pow 10 (t - 1) <= Nat.fromDigits (List.take k (Nat.digits x)))
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
theorem writtenTwiceOf (p: List Nat) (k: Nat) (hk: List.length p = k): writtenAs (List.append p p) k 2 = True :=
  Decidable.toBoolOf (List.decEq (\a b => Nat.decEq a b) (List.concat (List.replicate 2 (List.take k (List.append p p)))) (List.append p p))
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
theorem blockCount (x: Nat): (k: Nat) -> 1 <= k ->
    List.sumBy (\b => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
      = Nat.keepIf x (writtenAs (Nat.digits x) k 2)
  | Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ j, h =>
    match hq: writtenAs (Nat.digits x) (Succ j) 2 with
      | True =>
        List.sumRangeOne (\b => writeTimes (Succ j) b 2 == x) (\b => x) (Nat.fromDigits (List.take (Succ j) (Nat.digits x)))
          (Decidable.toBoolOf (Nat.decEq (writeTimes (Succ j) (Nat.fromDigits (List.take (Succ j) (Nat.digits x))) 2) x) (twiceValue x (Succ j) hq))
          (\b hb => twiceInjective (Succ j) b (Nat.fromDigits (List.take (Succ j) (Nat.digits x)))
            (Eq.trans (Decidable.toBoolSound (Nat.decEq (writeTimes (Succ j) b 2) x) hb) (Eq.sym (twiceValue x (Succ j) hq))))
          (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
          (twiceAbove x (Succ j) hq)
          (calc Nat.fromDigits (List.take (Succ j) (Nat.digits x))
            _ < Nat.pow 10 (Succ j)                                  := twiceBelow x (Succ j) hq
            _ = Nat.pow 10 j + (Nat.pow 10 (Succ j) - Nat.pow 10 j) := Eq.sym (Nat.addSubCancel (Nat.pow 10 j) (Nat.pow 10 (Succ j)) (Nat.powTenPredLe (Succ j))))
      | False =>
        List.sumRangeNone (\b => writeTimes (Succ j) b 2 == x) (\b => x) (Nat.pow 10 (Succ j) - Nat.pow 10 j) (Nat.pow 10 j)
          (\b h1 h2 => Decidable.toBoolOfNot (Nat.decEq (writeTimes (Succ j) b 2) x)
            (\e => Bool.trueNotFalse (Eq.trans
              (Eq.sym (J (\y q => writtenAs (Nat.digits y) (Succ j) 2 = True)
                (twiceDigits j b h1
                  (calc b
                    _ < Nat.pow 10 j + (Nat.pow 10 (Succ j) - Nat.pow 10 j) := h2
                    _ = Nat.pow 10 (Succ j) := Nat.addSubCancel (Nat.pow 10 j) (Nat.pow 10 (Succ j)) (Nat.powTenPredLe (Succ j))))
                e))
              hq)))

-- One block length, as a sum over the ids of the range.
theorem blocksAsIds (r: Range) (k: Nat):
    repeatedSpec r k 2
      = List.sumBy (\x => List.sumBy (\b => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
          (List.rangeFrom (r.to + 1 - r.from) r.from) :=
  calc repeatedSpec r k 2
    -- filtering the block ids by the range is summing "the id if it is in the range"
    _ = List.sumBy (\y => Nat.keepIf y (r.from <= y && y <= r.to)) (List.map (\b => writeTimes k b 2) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
        := List.sumFilter (\x => r.from <= x && x <= r.to) (List.map (\b => writeTimes k b 2) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
    _ = List.sumBy (\b => Nat.keepIf (writeTimes k b 2) (r.from <= writeTimes k b 2 && writeTimes k b 2 <= r.to)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
        := List.sumByMap (\y => Nat.keepIf y (r.from <= y && y <= r.to)) (\b => writeTimes k b 2) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
    -- and, for each block, "the id if it is in the range" is the sum over the range ids that equal it
    _ = List.sumBy (\b => List.sumBy (\x => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (r.to + 1 - r.from) r.from)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
        := List.sumByCongr (\b => Nat.keepIf (writeTimes k b 2) (r.from <= writeTimes k b 2 && writeTimes k b 2 <= r.to))
             (\b => List.sumBy (\x => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (r.to + 1 - r.from) r.from))
             (\b => Eq.sym (sumIdsEq r.from r.to (writeTimes k b 2)))
             (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))
    _ = List.sumBy (\x => List.sumBy (\b => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))) (List.rangeFrom (r.to + 1 - r.from) r.from)
        := List.sumBySwap (\b x => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (r.to + 1 - r.from) r.from) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)))

theorem twiceIds (r: Range) (k: Nat) (hk: 1 <= k):
    repeatedSpec r k 2 = List.sumBy (\x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids :=
  Eq.trans (blocksAsIds r k)
    (List.sumByCongr (\x => List.sumBy (\b => Nat.keepIf x (writeTimes k b 2 == x)) (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))
      (\x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) (\x => blockCount x k hk) r.ids)

-- (a') A block written twice: the arithmetic sum is the sum of the ids in
-- the range whose digits are some k-digit block written twice.
theorem repeatedTwice (r: Range) (k: Nat) (hk: 1 <= k):
    repeated r k 2 = (r.ids |> .filter (\x => writtenAs (Nat.digits x) k 2) |> .sum) :=
  calc repeated r k 2
    _ = repeatedSpec r k 2 := repeatedCorrect r k 2
    _ = List.sumBy (\x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids := twiceIds r k hk
    _ = (r.ids |> .filter (\x => writtenAs (Nat.digits x) k 2) |> .sum) := Eq.sym (List.sumFilter (\x => writtenAs (Nat.digits x) k 2) r.ids)

def parseRanges (t: Text): List Range := t.trim.split ',' |> .mapMaybe Range.parse

def example: Text := "11-22,95-115,998-1012,1188511880-1188511890,222220-222224,1698522-1698528,446443-446449,38593856-38593862,565653-565659,824824821-824824827,2121212118-2121212124"

def range (from to: Nat): Range := { from, to }

def exampleRanges: List Range := parseRanges example

test "example" := (solvePart1 exampleRanges, solvePart2 exampleRanges) == (1227775554, 4174379265)
test "parse" := parseRanges "4-14,1490-3407\n" == [range 4 14, range 1490 3407]

-- Cross-check against brute force ---------------------------------------
--
-- Both parts compared with the obvious method on many small ranges: look at
-- every id's digits. (Both are also proved: part 1 below, part 2 in
-- part2proof.sw.)

-- Part 1: written twice; part 2: written two or more times.
def doubled (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (\k => writtenAs ds k 2)

def repeats (x: Nat): Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (\k => List.rangeFrom ds.length 2 |> .any (\n => writtenAs ds k n))

def bruteSum (invalid: Nat -> Bool) (r: Range): Nat :=
  r.ids |> .filter invalid |> .sum

def agrees (r: Range): Bool :=
  weighted twice r == bruteSum doubled r && invalid r == bruteSum repeats r

-- Ranges of 40 ids starting every 13 up to 2000, and some that cross into
-- more digits.
def checkRanges: List Range :=
  (List.rangeFrom 154 0 |> .map (\i => range (13 * i) (13 * i + 39)))
    ++ [range 95 115, range 990 1010, range 9990 10010, range 99990 100010, range 111100 111200, range 999990 1000010]

test "brute force agrees" := checkRanges.all agrees

-- Ids of 11 to 20 digits, around 1 written 11, 12 and 13 times, 12 written 6
-- times, 1234 written 3 times, 17 ones, 10 written 10 times, and across into
-- 12 digits: part 2 against walking the ids.
def longRanges: List Range :=
  [range 11111111100 11111111120, range 111111111101 111111111121, range 1111111111100 1111111111120,
   range 121212121202 121212121222, range 123412341224 123412341244, range 99999999989 100000000009,
   range 11111111111111101 11111111111111121, range 10101010101010101000 10101010101010101020]

test "long ids" := longRanges.all (\r => invalid r == bruteSum repeats r)
test "long ids found" := List.map invalid longRanges == [11111111111, 111111111111, 1111111111111, 121212121212, 123412341234, 99999999999, 11111111111111111, 10101010101010101010]

-- Why part 1 is right (b): `part1BlocksCorrect` says the printed part 1 is
-- `part1Blocks`, the brute-force sum over every range and block length of the
-- blocks written twice; (c) below says that is the puzzle's own sum. Part 2
-- is proved in part2proof.sw (`Aoc.Day02.Proofs.part2Correct`).

-- Brute force for part 1: in each range, every block length up to the
-- number of digits of `to` (a longer block makes a longer id), every block of
-- that length written twice.
def part1Blocks (ranges: List Range): Nat :=
  ranges |> .sumBy (\r => List.rangeFrom (Nat.digits r.to).length 1 |> .sumBy (\k => repeatedSpec r k 2))

-- If every block from `low` on makes an id above `to`, none is in the range.
theorem noneInRange (from: Nat) (to: Nat) (w: Nat -> Nat) (low: Nat) (big: (b: Nat) -> low <= b -> Nat.leq (w b) to = False):
    (c: Nat) -> (s: Nat) -> low <= s -> List.sum (List.filter (\x => from <= x && x <= to) (List.map w (List.rangeFrom c s))) = 0
  | Zero,   s, h => rfl
  | Succ c, s, h =>
    Eq.trans (Eq.cong List.sum (List.filterSkip (\x => from <= x && x <= to) (w s) (List.map w (List.rangeFrom c (Succ s))) (Nat.betweenOver from to (w s) (big s h))))
      (noneInRange from to w low big c (Succ s) (Nat.leTrans low s (Succ s) h (Nat.leSucc s)))

-- A block of k digits written twice has 2k digits, too many when `to` has fewer.
theorem tooLong (r: Range): (k: Nat) -> Nat.leq (k * 2) (List.length (Nat.digits r.to)) = False -> repeatedSpec r k 2 = 0
  | Zero,   h => Void.exfalso (Bool.trueNotFalse h)
  | Succ k, h =>
    noneInRange r.from r.to (\b => writeTimes (Succ k) b 2) (Nat.pow 10 k)
      (\b hb => Nat.leqFalseOfLess r.to (b * Nat.pow 10 (Succ k) + b)
        (calc r.to
          _ < Nat.pow 10 (List.length (Nat.digits r.to))  := Nat.ltPowTenDigits r.to
          _ <= Nat.pow 10 (k + Succ k)
              := Nat.powMono 9 (List.length (Nat.digits r.to)) (k + Succ k)
                   (calc List.length (Nat.digits r.to)
                     _ <= Succ (k * 2) := Nat.leqFalse (Succ k * 2) (List.length (Nat.digits r.to)) h
                     _ = k + Succ k    := Eq.trans (Eq.cong Succ (Eq.trans (Nat.mulSucc k 1) (Eq.cong (\t => k + t) (Nat.mulOne k)))) (Eq.sym (Nat.addSucc k k)))
          _ = Nat.pow 10 k * Nat.pow 10 (Succ k)          := Nat.powAdd 10 k (Succ k)
          _ <= b * Nat.pow 10 (Succ k)                    := Nat.leMulRight (Nat.pow 10 k) b (Nat.pow 10 (Succ k)) hb
          _ <= b * Nat.pow 10 (Succ k) + b                := Nat.leAddRight (b * Nat.pow 10 (Succ k)) b))
      (Nat.pow 10 (Succ k) - Nat.pow 10 k) (Nat.pow 10 k) (Nat.leRefl (Nat.pow 10 k))

-- Repeat counts from 3 on count for nothing in part 1.
theorem otherCounts (r: Range) (k: Nat) (size: Nat): (c: Nat) -> (s: Nat) ->
    List.sumBy (\n => if Nat.leq (k * n) size then twice n * repeated r k n else 0) (List.rangeFrom c (Succ (Succ (Succ s)))) = 0
  | Zero,   s => rfl
  | Succ c, s =>
    match h: Nat.leq (k * Succ (Succ (Succ s))) size with
      | True  => otherCounts r k size c (Succ s)
      | False => otherCounts r k size c (Succ s)

-- One block length's terms: the block written twice, if it fits.
theorem twiceTerms (r: Range): (k: Nat) -> (size: Nat) -> 1 <= k -> (Nat.leq (k * 2) size = False -> repeatedSpec r k 2 = 0) ->
    List.sumBy (\n => if Nat.leq (k * n) size then twice n * repeated r k n else 0) (List.rangeFrom (size - 1) 2) = repeatedSpec r k 2
  | Zero,   size,          hk, fits => Void.exfalso (Bool.falseNotTrue hk)
  | Succ k, Zero,          hk, fits => Eq.sym (fits rfl)
  | Succ k, Succ Zero,     hk, fits => Eq.sym (fits rfl)
  | Succ k, Succ (Succ s), hk, fits =>
    let f: Nat -> Nat := \n => if Nat.leq (Succ k * n) (Succ (Succ s)) then twice n * repeated r (Succ k) n else 0
    match h: Nat.leq (Succ k * 2) (Succ (Succ s)) with
      | True =>
        -- (the match has already chosen the first term, n = 2)
        calc List.foldLeft (\acc n => acc + f n) (1 * repeated r (Succ k) 2) (List.rangeFrom s 3)
          _ = 1 * repeated r (Succ k) 2 + List.sumBy f (List.rangeFrom s 3) := List.sumByFrom f (1 * repeated r (Succ k) 2) (List.rangeFrom s 3)
          _ = 1 * repeated r (Succ k) 2 + 0 := rewrite otherCounts r (Succ k) (Succ (Succ s)) s 0
          _ = repeated r (Succ k) 2         := Eq.trans (Nat.addZero (1 * repeated r (Succ k) 2)) (Nat.addZero (repeated r (Succ k) 2))
          _ = repeatedSpec r (Succ k) 2     := repeatedCorrect r (Succ k) 2
      | False => Eq.trans (otherCounts r (Succ k) (Succ (Succ s)) s 0) (Eq.sym (fits rfl))

theorem weightedTwice (r: Range): weighted twice r = (List.rangeFrom (Nat.digits r.to).length 1 |> .sumBy (\k => repeatedSpec r k 2)) :=
  List.sumRangeCongr
    (\k => List.sumBy (\n => if Nat.leq (k * n) (List.length (Nat.digits r.to)) then twice n * repeated r k n else 0) (List.rangeFrom (List.length (Nat.digits r.to) - 1) 2))
    (\k => repeatedSpec r k 2) (List.length (Nat.digits r.to)) 1
    (\k k1 k2 => twiceTerms r k (List.length (Nat.digits r.to)) k1 (tooLong r k))

-- (b) Part 1 is the brute-force sum over blocks.
theorem part1BlocksCorrect (ranges: List Range): solvePart1 ranges = part1Blocks ranges :=
  List.sumByCongr (weighted twice) (\r => List.rangeFrom (Nat.digits r.to).length 1 |> .sumBy (\k => repeatedSpec r k 2)) weightedTwice ranges

-- Why part 1 is right (c): `part1Correct` says the printed part 1 is
-- `part1Spec`, the puzzle's own method: walk every id of every range, keep
-- the ids whose digits are some block written twice (`doubled`), add them up.
--
-- The block walk of (b) adds the same ids. For each block length k it adds
-- the ids whose digits are a k-digit block written twice (`twiceIds`, from
-- `repeatedTwice`'s proof). An id is that for one k at most, half its
-- number of digits (`twiceHalf`), and that k is below the number of digits
-- of `to` (`twiceAtLeast`), so swapping the sums over ids and block lengths
-- leaves each doubled id added once.

def part1Spec (ranges: List Range): Nat :=
  ranges |> .sumBy (\r => r.ids |> .filter doubled |> .sum)

test "part 1 spec" := part1Spec exampleRanges == 1227775554


-- For one id `x` up to `to`: over all block lengths, the blocks written twice
-- that make `x` add up to `x` if `x` is doubled, else 0.
theorem idCount (to: Nat) (x: Nat) (hx: x <= to):
    List.sumBy (\k => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) (List.rangeFrom (List.length (Nat.digits to)) 1) = Nat.keepIf x (doubled x) :=
  match hd: doubled x with
    | True =>
      List.anyRangeElim (\k => writtenAs (Nat.digits x) k 2)
        (List.sumBy (\k => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) (List.rangeFrom (List.length (Nat.digits to)) 1) = x)
        (List.length (Nat.digits x)) 1 hd
        (\k0 h1 h2 hk0 =>
          List.sumRangeOne (\k => writtenAs (Nat.digits x) k 2) (\k => x) k0 hk0
            (\k hk => Eq.trans (Eq.sym (Nat.halfDouble k))
              (Eq.trans (Eq.cong (\t => t / 2) (Eq.trans (twiceHalf x k hk) (Eq.sym (twiceHalf x k0 hk0)))) (Nat.halfDouble k0)))
            (List.length (Nat.digits to)) 1 h1
            (Nat.lessLe k0 (List.length (Nat.digits to))
              (Nat.powTenLt k0 (List.length (Nat.digits to)) x (twiceAtLeast x k0 hk0) (Nat.leTrans (Succ x) (Succ to) (Nat.pow 10 (List.length (Nat.digits to))) hx (Nat.ltPowTenDigits to)))))
    | False =>
      List.sumRangeNone (\k => writtenAs (Nat.digits x) k 2) (\k => x) (List.length (Nat.digits to)) 1
        (\k h1 h2 =>
          match t: writtenAs (Nat.digits x) k 2 with
            | True =>
              Void.exfalso (Bool.trueNotFalse (Eq.trans
                (Eq.sym (List.anyRangeIntro (\k => writtenAs (Nat.digits x) k 2) (List.length (Nat.digits x)) 1 k h1
                  (Nat.leCongRight k (k + k) (List.length (Nat.digits x)) (twiceHalf x k t) (Nat.leAddRight k k)) t))
                hd))
            | False => rfl)


-- One range: the block walk is the id walk.
theorem rangeBlocksIds (r: Range):
    List.sumBy (\k => repeatedSpec r k 2) (List.rangeFrom (List.length (Nat.digits r.to)) 1) = List.sum (List.filter doubled r.ids) :=
  calc List.sumBy (\k => repeatedSpec r k 2) (List.rangeFrom (List.length (Nat.digits r.to)) 1)
    -- block length by block length, the ids whose digits are that block written twice...
    _ = List.sumBy (\k => List.sumBy (\x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids) (List.rangeFrom (List.length (Nat.digits r.to)) 1)
        := List.sumRangeCongr (\k => repeatedSpec r k 2) (\k => List.sumBy (\x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids)
             (List.length (Nat.digits r.to)) 1 (\k h1 h2 => twiceIds r k h1)
    -- ...id by id, the block lengths that make it...
    _ = List.sumBy (\x => List.sumBy (\k => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) (List.rangeFrom (List.length (Nat.digits r.to)) 1)) r.ids
        := List.sumBySwap (\k x => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) r.ids (List.rangeFrom (List.length (Nat.digits r.to)) 1)
    -- ...which is the id once if it is doubled, and not at all if not.
    _ = List.sumBy (\x => Nat.keepIf x (doubled x)) r.ids
        := List.sumRangeCongr (\x => List.sumBy (\k => Nat.keepIf x (writtenAs (Nat.digits x) k 2)) (List.rangeFrom (List.length (Nat.digits r.to)) 1))
             (\x => Nat.keepIf x (doubled x)) (r.to + 1 - r.from) r.from
             (\x h1 h2 => idCount r.to x (rangeEnd r.from r.to x h1 h2))
    _ = List.sum (List.filter doubled r.ids) := Eq.sym (List.sumFilter doubled r.ids)

-- The block walk and the id walk agree on every input.
theorem blocksAreIds (ranges: List Range): part1Blocks ranges = part1Spec ranges :=
  List.sumByCongr (\r => List.sumBy (\k => repeatedSpec r k 2) (List.rangeFrom (List.length (Nat.digits r.to)) 1))
    (\r => List.sum (List.filter doubled r.ids)) rangeBlocksIds ranges

-- (c) Part 1 is the sum of the ids, in all the ranges, whose digits are some
-- block written twice.
theorem part1Correct (ranges: List Range): solvePart1 ranges = part1Spec ranges :=
  Eq.trans (part1BlocksCorrect ranges) (blocksAreIds ranges)
