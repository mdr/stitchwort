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
-- - `RepetitionTemplate.sumIn` adds the ids of the range whose digits are a block of the
--   template's length written the template's number of copies (`repeatedIds`). The
--   program's sum over the templates is a grid of block lengths and copies
--   (`sumOfIdsWrittenRepeatedlyGrid`); swapping the sums over ids, block lengths and
--   copies finishes it (`weightedIds`, `rangeWeighted`).
--   The signed total is the natural answer embedded, so `Int.toNat` gives it back.

namespace Aoc.Day02.Proofs
import Aoc.Common (Range)
import Aoc.Day02 (..)
import Aoc.Day02.Spec (..)
import Std (Bool, DecEq, Decidable, Eq, Int, List, Nat, Void)

-- (1) n copies ------------------------------------------------------------
-- The n-copies lemmas (`repeatedIds`, `repCount`, `collapse`, `copies`,
-- `idsBelow`) are in Repeated.sw, shared with part 1.

-- (2) The weights ------------------------------------------------------------
-- Over the divisors of m from 2 on, `copiesWeight` adds up to 1 when m >= 2, and to
-- 0 when m = 1 (`weightsOne`).

-- The weights w of the divisors of m among 2, 3, ..., c + 1, added up.
def divisorWeights (w: Nat → Int) (m: Nat) (c: Nat): Int :=
  List.rangeFrom c 2 |> .sumBy (d => if Nat.divides d m then w d else 0)

-- A guard that holds takes the first branch.
theorem guardHolds [p: Prop] [a: Type]: (d: Decidable p) → p → (x: a) → (y: a) → Decidable.elim d (g => x) (r => y) = x
  | Yes q, h, x, y => rfl
  | No r, h, x, y => Void.exfalso (r h)

-- The weight of m = j + 2 is 1, less the weights of its divisors below m
-- (`weight.unfold`, with the guard `d < m` discharged for each d of the run).
theorem weightBelow (j: Nat): copiesWeight (Succ (Succ j)) = 1 - divisorWeights copiesWeight (Succ (Succ j)) j :=
  let guarded: Nat → Int := d => if h: d < Succ (Succ j) then (if Nat.divides d (Succ (Succ j)) then copiesWeight d else 0) else 0
  let plain: Nat → Int := d => if Nat.divides d (Succ (Succ j)) then copiesWeight d else 0
  calc copiesWeight (Succ (Succ j))
    _ = 1 - List.sumBy (List.rangeFrom (j + 1 - 1) 2) guarded := copiesWeight.unfold (Succ (Succ j))
    _ = 1 - List.sumBy (List.rangeFrom j 2) guarded := rewrite (omega: j + 1 - 1 = j)
    _ = 1 - List.sumBy (List.rangeFrom j 2) plain
      := rewrite guardHolds

theorem divisorWeightsTop (w: Nat → Int) (j: Nat): divisorWeights w (Succ (Succ j)) (Succ j) = divisorWeights w (Succ (Succ j)) j + w (Succ (Succ j)) :=
  let f: Nat → Int := d => if Nat.divides d (Succ (Succ j)) then w d else 0
  calc List.sumBy (List.rangeFrom (Succ j) 2) f
    _ = List.sumBy (List.rangeFrom (j + 1) 2) f := Eq.cong (t => List.sumBy (List.rangeFrom t 2) f) (ring: Succ j = j + 1)
    _ = List.sumBy (List.append (List.rangeFrom j 2) (List.rangeFrom 1 (2 + j))) f := Eq.cong (.sumBy f) (List.rangeFromAppend j 1 2)
    _ = List.sumBy (List.rangeFrom j 2) f + List.sumBy (List.rangeFrom 1 (2 + j)) f := List.sumByAppend (List.rangeFrom j 2) (List.rangeFrom 1 (2 + j)) f
    _ = List.sumBy (List.rangeFrom j 2) f + f (Succ (Succ j)) := ring
    _ = List.sumBy (List.rangeFrom j 2) f + w (Succ (Succ j))
      := rewrite Nat.dividesSelf (Succ (Succ j))

-- The key fact: the weights of the divisors of m from 2 on add up to 1.
theorem weightsOne: (m: Nat) → 1 ≤ m → divisorWeights copiesWeight m (m - 1) = (Bool.toNat (Nat.leq 2 m)).toInt
  | Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ Zero, h => rfl
  | Succ (Succ j), h =>
    calc divisorWeights copiesWeight (Succ (Succ j)) (Succ j)
      _ = divisorWeights copiesWeight (Succ (Succ j)) j + copiesWeight (Succ (Succ j)) := divisorWeightsTop copiesWeight j
      _ = divisorWeights copiesWeight (Succ (Succ j)) j + (1 - divisorWeights copiesWeight (Succ (Succ j)) j)
        := rewrite weightBelow j
      _ = 1 := ring

-- Divisors of m beyond m count for nothing.
theorem divisorWeightsAll (w: Nat → Int): (m: Nat) → 1 ≤ m → (c: Nat) → m ≤ Succ c → divisorWeights w m c = divisorWeights w m (m - 1)
  | Zero, hm, c, hc => Void.exfalso (Bool.falseNotTrue hm)
  | Succ k, hm, c, hc =>
    let f: Nat → Int := d => if Nat.divides d (Succ k) then w d else 0
    calc List.sumBy (List.rangeFrom c 2) f
      _ = List.sumBy (List.rangeFrom (k + (c - k)) 2) f := Eq.cong (t => List.sumBy (List.rangeFrom t 2) f) (omega: c = k + (c - k))
      _ = List.sumBy (List.append (List.rangeFrom k 2) (List.rangeFrom (c - k) (2 + k))) f := Eq.cong (.sumBy f) (List.rangeFromAppend k (c - k) 2)
      _ = List.sumBy (List.rangeFrom k 2) f + List.sumBy (List.rangeFrom (c - k) (2 + k)) f := List.sumByAppend (List.rangeFrom k 2) (List.rangeFrom (c - k) (2 + k)) f
      _ = List.sumBy (List.rangeFrom k 2) f + 0
        := rewrite Nat.dividesSmall _ (Succ k) rfl, List.sumByZero [add := Int.instAdd] (List.rangeFrom (c - k) (2 + k))
      _ = List.sumBy (List.rangeFrom k 2) f := ring

theorem mulKeep (v: Int) (x: Nat): (b: Bool) → v * (Nat.keepIf x b).toInt = x.toInt * (if b then v else 0)
  | True => ring
  | False => ring

-- (3) Periods ----------------------------------------------------------------

-- Rotating the first `len` values of g by p places leaves them unchanged.
def Period (g: Nat → Nat) (len: Nat) (hl: len ≠ 0) (p: Nat): Prop := (i: Nat) → i < len → g ((i + p) % len) = g i

theorem periodZero (g: Nat → Nat) (len: Nat) (hl: len ≠ 0): Period g len hl 0 :=
  i hi => Eq.cong g (Eq.trans (Eq.cong (y => y % len) (ring: i + 0 = i)) (Nat.modSmall i len hi))

theorem periodLen (g: Nat → Nat) (len: Nat) (hl: len ≠ 0): Period g len hl len :=
  i hi => Eq.cong g (Eq.trans (Eq.cong (y => y % len) (ring: i + len = len + i)) (Eq.trans (Nat.addModSelf len i) (Nat.modSmall i len hi)))

-- Doing one rotation and then the other is a rotation too.
theorem periodAdd (g: Nat → Nat) (len: Nat) (hl: len ≠ 0) (p: Nat) (q: Nat) (hp: Period g len hl p) (hq: Period g len hl q): Period g len hl (p + q) :=
  i hi =>
    calc g ((i + (p + q)) % len)
      _ = g (((i + p) + q) % len) := rewrite (ring: i + (p + q) = i + p + q)
      _ = g (((i + p) % len + q) % len) := Eq.cong g (Eq.sym (Nat.modAddMod (i + p) q len))
      _ = g ((i + p) % len) := hq ((i + p) % len) (Nat.modLess (i + p) len hl)
      _ = g i := hp i hi

theorem periodSub (g: Nat → Nat) (len: Nat) (hl: len ≠ 0) (p: Nat) (q: Nat) (hp: Period g len hl p) (hq: Period g len hl q) (hle: q ≤ p): Period g len hl (p - q) :=
  i hi =>
    calc g ((i + (p - q)) % len)
      _ = g (((i + (p - q)) % len + q) % len) := Eq.sym (hq ((i + (p - q)) % len) (Nat.modLess (i + (p - q)) len hl))
      _ = g ((i + (p - q) + q) % len) := Eq.cong g (Nat.modAddMod (i + (p - q)) q len)
      _ = g ((i + p) % len)
        := rewrite (omega: i + (p - q) + q = i + p)
      _ = g i := hp i hi

theorem periodMul (g: Nat → Nat) (len: Nat) (hl: len ≠ 0) (p: Nat) (hp: Period g len hl p): (t: Nat) → Period g len hl (t * p)
  | Zero, i, hi => periodZero g len hl i hi
  | Succ t, i, hi => periodAdd g len hl p (t * p) hp (j hj => periodMul g len hl p hp t j hj) i hi

-- The same as a test, which a search can run.
def isPeriod (g: Nat → Nat) (len: Nat) (hl: len ≠ 0) (p: Nat): Bool := List.range len |> .all (i => g ((i + p) % len) == g i)

theorem periodOfTest (g: Nat → Nat) (len: Nat) (hl: len ≠ 0) (p: Nat) (h: isPeriod g len hl p = True): Period g len hl p :=
  i hi => DecEq.sound (g ((i + p) % len)) (g i) (List.allRangeElim (i => g ((i + p) % len) == g i) len 0 h i omega hi)

theorem periodTest (g: Nat → Nat) (len: Nat) (hl: len ≠ 0) (p: Nat) (h: Period g len hl p): isPeriod g len hl p = True :=
  List.allRangeIntro (i => g ((i + p) % len) == g i) len 0 (i h1 h2 => Decidable.toBoolOf (Nat.decEq (g ((i + p) % len)) (g i)) (h i h2))

-- A period below the smallest positive one, `Succ j`, is 0.
theorem periodBelow (g: Nat → Nat) (len: Nat) (hl: len ≠ 0) (j: Nat) (hmin: (r: Nat) → r < j → isPeriod g len hl (Succ r) = False):
    (r: Nat) → Period g len hl r → r < Succ j → r = 0
  | Zero, hr, lt => rfl
  | Succ r, hr, lt => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (periodTest g len hl (Succ r) hr)) (hmin r lt)))

-- The heart: every period is a multiple of the smallest positive one (the
-- remainder of the division is a smaller period).
theorem periodDvd (g: Nat → Nat) (len: Nat) (hl: len ≠ 0) (j: Nat) (hp0: Period g len hl (Succ j))
    (hmin: (r: Nat) → r < j → isPeriod g len hl (Succ r) = False) (p: Nat) (hp: Period g len hl p): p % Succ j = 0 :=
  let t := p / Succ j
  let rest: Period g len hl (p - t * Succ j) :=
    periodSub g len hl p (t * Succ j) hp (periodMul g len hl (Succ j) hp0 t) (Nat.divMulLe p (Succ j) (Nat.succNotZero j))
  let e: p - t * Succ j = p % Succ j := omega [Nat.divModEq p (Succ j) (Nat.succNotZero j)]
  periodBelow g len hl j hmin (p % Succ j) (rewrite e at rest) (Nat.modLess p (Succ j) (Nat.succNotZero j))

-- (4) Blocks are periods -----------------------------------------------------

-- The digit at position i (0 past the end).
def digitAt (ds: List Nat) (i: Nat): Nat := List.getOr ds 0 i

-- Digits that are their first k digits written n times: each digit is the
-- one at its position within the first k.
theorem writtenBlock (ds: List Nat) (k: Nat) (n: Nat) [auto hk: k ≠ 0] (hn: 1 ≤ n) (e: k * n = ds.length) (hw: writtenAs ds k n = True)
    (j: Nat) (hj: j < ds.length): digitAt ds j = digitAt ds (j % k) :=
  calc List.getOr ds 0 j
    _ = List.getOr (List.concat (List.replicate n (List.take ds k))) 0 j
      := Eq.cong (l => List.getOr l 0 j) (Eq.sym (DecEq.sound (List.concat (List.replicate n (List.take ds k))) ds hw))
    _ = List.getOr (List.take ds k) 0 (j % k)
      := List.getOrConcatReplicate (List.take ds k) 0 k (List.lengthTake ds k (omega [Nat.leMulPos k n hn])) n j
        omega
    _ = List.getOr ds 0 (j % k) := List.getOrTake ds 0 k (j % k) (Nat.modLess j k hk)

theorem writtenPeriod (ds: List Nat) (hl: ds.length ≠ 0) (k: Nat) (n: Nat) [auto hk: k ≠ 0] (hn: 1 ≤ n) (e: k * n = ds.length)
    (hw: writtenAs ds k n = True): Period (digitAt ds) ds.length hl k :=
  i hi =>
    calc digitAt ds ((i + k) % ds.length)
      _ = digitAt ds ((i + k) % ds.length % k) := writtenBlock ds k n hn e hw ((i + k) % ds.length) (Nat.modLess (i + k) ds.length hl)
      _ = digitAt ds ((i + k) % k) := Eq.cong (digitAt ds) (Nat.modModOfMul (i + k) ds.length k n omega)
      _ = digitAt ds (i % k) := Eq.cong (digitAt ds) (Eq.trans (Eq.cong (y => y % k) (ring: i + k = k + i)) (Nat.addModSelf k i))
      _ = digitAt ds i := Eq.sym (writtenBlock ds k n hn e hw i hi)

-- With period k, each digit is the one at its position within the first k.
theorem periodBlock (ds: List Nat) (hl: ds.length ≠ 0) (k: Nat) [auto hk: k ≠ 0] (hp: Period (digitAt ds) ds.length hl k)
    (i: Nat) (hi: i < ds.length): digitAt ds i = digitAt ds (i % k) :=
  calc digitAt ds i
    _ = digitAt ds (i % ds.length) := Eq.cong (digitAt ds) (Eq.sym (Nat.modSmall i ds.length hi))
    _ = digitAt ds ((i % k + (i / k) * k) % ds.length)
      := Eq.cong (y => digitAt ds (y % ds.length)) (Eq.trans (Nat.divModEq i k hk) (Nat.addComm ((i / k) * k) (i % k)))
    _ = digitAt ds (i % k)
      := periodMul (digitAt ds) ds.length hl k hp (i / k) (i % k) omega

theorem periodWritten (ds: List Nat) (hl: ds.length ≠ 0) (k: Nat) (n: Nat) [auto hk: k ≠ 0] (hn: 1 ≤ n) (e: k * n = ds.length)
    (hp: Period (digitAt ds) ds.length hl k): writtenAs ds k n = True :=
  let ht: List.length (List.take ds k) = k := List.lengthTake ds k (omega [Nat.leMulPos k n hn])
  let len: List.length (List.concat (List.replicate n (List.take ds k))) = n * k :=
    Eq.trans (List.lengthConcatReplicate (List.take ds k) n) (Eq.cong (t => n * t) ht)
  Decidable.toBoolOf (List.decEq (a b => Nat.decEq a b) (List.concat (List.replicate n (List.take ds k))) ds)
    (List.extGetOr 0 (List.concat (List.replicate n (List.take ds k))) ds omega
      (i hi =>
        calc List.getOr (List.concat (List.replicate n (List.take ds k))) 0 i
          _ = List.getOr (List.take ds k) 0 (i % k) := List.getOrConcatReplicate (List.take ds k) 0 k ht n i omega
          _ = List.getOr ds 0 (i % k) := List.getOrTake ds 0 k (i % k) (Nat.modLess i k hk)
          _ = List.getOr ds 0 i
            := Eq.sym (periodBlock ds hl k hp i omega)))

-- (5) One id -----------------------------------------------------------------

def digitCount (x: Nat): Nat := List.length (Nat.digits x)

theorem digitCountNonZero (x: Nat): digitCount x ≠ 0 := Nat.nonzeroOfPos (digitCount x) (Nat.digitsNonEmpty x)

-- x's digits have period p.
def periodOf (x: Nat) (p: Nat): Bool := isPeriod (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) p

-- x's smallest positive period is `Succ (periodIndex x)`: the first p in
-- 1, 2, ..., digitCount x that passes (the digit count always does).
def periodIndex (x: Nat): Nat := Nat.firstFrom (j => periodOf x (Succ j)) (digitCount x) 0

def smallestPeriod (x: Nat): Nat := Succ (periodIndex x)

-- How many times x's smallest block is written.
def blockCount (x: Nat): Nat := digitCount x / smallestPeriod x

test "smallest blocks" := List.map [7, 1212, 123123123, 1213] blockCount == [1, 2, 3, 1]

theorem smallestIsPeriod (x: Nat): Period (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (smallestPeriod x) :=
  let top: Succ (digitCount x - 1) = digitCount x := omega [Nat.digitsNonEmpty x]
  periodOfTest (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (smallestPeriod x)
    (Nat.firstFromFound (j => periodOf x (Succ j)) (digitCount x) 0 (digitCount x - 1) omega omega
      (rewrite top in periodTest (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (digitCount x) (periodLen (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x))))

theorem smallestDivides (x: Nat) (p: Nat) (hp: Period (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) p): p % smallestPeriod x = 0 :=
  periodDvd (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (periodIndex x) (smallestIsPeriod x)
    (r hr => Nat.firstFromBefore (j => periodOf x (Succ j)) (digitCount x) 0 r omega hr) p hp

theorem countTimesPeriod (x: Nat): digitCount x = blockCount x * smallestPeriod x :=
  calc digitCount x
    _ = blockCount x * smallestPeriod x + digitCount x % smallestPeriod x := Nat.divModEq (digitCount x) (smallestPeriod x) (Nat.succNotZero (periodIndex x))
    _ = blockCount x * smallestPeriod x
      := omega [smallestDivides x (digitCount x) (periodLen (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x))]

theorem blockCountPos (x: Nat): 1 ≤ blockCount x :=
  match e: blockCount x with
    | Zero => Void.exfalso (Bool.falseNotTrue (rewrite countTimesPeriod x, e at (Nat.digitsNonEmpty x: 1 ≤ digitCount x)))
    | Succ k => rfl

theorem blockCountLe (x: Nat): blockCount x ≤ digitCount x :=
  omega [Nat.leMulPos (blockCount x) (smallestPeriod x) rfl, countTimesPeriod x]

-- A block of k digits written n times: n divides the block count.
theorem dividesOfWritten (x: Nat) (n: Nat) (hn: 2 ≤ n) (k: Nat) (hk1: 1 ≤ k) (hw: writtenAs (Nat.digits x) k n = True): Nat.divides n (blockCount x) = True :=
  let hk: k ≠ 0 := Nat.nonzeroOfPos k hk1
  let per := writtenPeriod (Nat.digits x) (digitCountNonZero x) k n omega (omega [repCount x k n hn hw]) hw
  -- k is t times the smallest period
  let t := k / smallestPeriod x
  let ek: k = t * smallestPeriod x :=
    omega [Nat.divModEq k (smallestPeriod x) (Nat.succNotZero (periodIndex x)), smallestDivides x k per]
  let eK: blockCount x = n * t :=
    Nat.mulSuccCancel (blockCount x) (n * t) (periodIndex x)
      (calc blockCount x * smallestPeriod x
        _ = digitCount x := Eq.sym (countTimesPeriod x)
        _ = n * k := Eq.sym (repCount x k n hn hw)
        _ = n * (t * smallestPeriod x) := Eq.cong (y => n * y) ek
        _ = n * t * smallestPeriod x := ring)
  rewrite (ring: t * n = n * t), <- eK at Nat.dividesMul n t

-- And back: if n divides the block count, the digits are a block written n times.
theorem writtenOfDivides (x: Nat) (n: Nat) (hn: 2 ≤ n): (t: Nat) → blockCount x = t * n → copies x n = True
  | Zero, e => omega [blockCountPos x]
  | Succ t, e =>
    let k := Succ t * smallestPeriod x
    let ekn: k * n = digitCount x :=
      calc (Succ t * smallestPeriod x) * n
        _ = blockCount x * smallestPeriod x := rewrite e in ring
        _ = digitCount x := Eq.sym (countTimesPeriod x)
    let hw: writtenAs (Nat.digits x) k n = True :=
      periodWritten (Nat.digits x) (digitCountNonZero x) k n omega ekn
        (periodMul (digitAt (Nat.digits x)) (digitCount x) (digitCountNonZero x) (smallestPeriod x) (smallestIsPeriod x) (Succ t))
    List.anyRangeIntro (k => writtenAs (Nat.digits x) k n) (digitCount x) 1 k rfl
      (omega [Nat.leMulPos k n omega]) hw

-- x's digits are a block written n times exactly when n divides the block count.
theorem copiesDivides (x: Nat) (n: Nat) (hn: 2 ≤ n): copies x n = Nat.divides n (blockCount x) :=
  Bool.eqOf (copies x n) (Nat.divides n (blockCount x))
    (h => List.anyRangeElim (k => writtenAs (Nat.digits x) k n) (Nat.divides n (blockCount x) = True) (digitCount x) 1 h
      (k h1 h2 hw => dividesOfWritten x n hn k h1 hw))
    (h => Nat.dividesElim (copies x n = True) n (blockCount x) h (t e => writtenOfDivides x n hn t e))

-- x repeats exactly when its smallest block is written at least twice.
theorem repeatsBlocks (x: Nat): repeats x = Nat.leq 2 (blockCount x) :=
  Bool.eqOf (repeats x) (Nat.leq 2 (blockCount x))
    (h => List.anyRangeElim (k => List.any (List.rangeFrom (digitCount x) 2) (n => writtenAs (Nat.digits x) k n)) (2 ≤ blockCount x) (digitCount x) 1 h
      (k h1 h2 hk => List.anyRangeElim (n => writtenAs (Nat.digits x) k n) (2 ≤ blockCount x) (digitCount x) 2 hk
        (n n1 n2 hw =>
          omega [Nat.dividesLe n (blockCount x) (blockCountPos x)
            (Eq.trans (Eq.sym (copiesDivides x n n1)) (List.anyRangeIntro (k => writtenAs (Nat.digits x) k n) (digitCount x) 1 k h1 h2 hw))])))
    (h => List.anyRangeElim (k => writtenAs (Nat.digits x) k (blockCount x)) (repeats x = True) (digitCount x) 1
      (Eq.trans (copiesDivides x (blockCount x) h) (Nat.dividesSelf (blockCount x)))
      (k h1 h2 hw => List.anyRangeIntro (k => List.any (List.rangeFrom (digitCount x) 2) (n => writtenAs (Nat.digits x) k n)) (digitCount x) 1 k h1 h2
        (List.anyRangeIntro (n => writtenAs (Nat.digits x) k n) (digitCount x) 2 (blockCount x) h
          (omega [blockCountLe x]) hw)))

-- One id's terms under weights w: every block length k up to `size` and
-- repeat count n from 2 to `size`.
def idTerms (w: Nat → Int) (size: Nat) (x: Nat): Int :=
  List.rangeFrom size 1 |> .sumBy (k => List.rangeFrom (size - 1) 2 |> .sumBy (n => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt))

-- They add up to x times the weights of the divisors of the block count.
theorem idTermsDivisors (w: Nat → Int) (size: Nat) (x: Nat) (hL: digitCount x ≤ size):
    idTerms w size x = x.toInt * divisorWeights w (blockCount x) (size - 1) :=
  calc idTerms w size x
    _ = List.sumBy (List.rangeFrom (size - 1) 2) (n => List.sumBy (List.rangeFrom size 1) (k => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt))
      := List.sumBySwap (List.rangeFrom (size - 1) 2) (List.rangeFrom size 1) (k n => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt)
    _ = List.sumBy (List.rangeFrom (size - 1) 2) (n => x.toInt * (if Nat.divides n (blockCount x) then w n else 0))
      := rewrite Int.sumByMulLeft (w _), <- Int.toIntSumBy _ (List.rangeFrom size 1), collapse x _ _ size hL, copiesDivides x,
        mulKeep (w _) x
    _ = x.toInt * divisorWeights w (blockCount x) (size - 1)
      := Int.sumByMulLeft x.toInt (n => if Nat.divides n (blockCount x) then w n else 0) (List.rangeFrom (size - 1) 2)

-- One id: its terms add up to x itself if x repeats, and to nothing if not.
theorem idWeight (size: Nat) (x: Nat) (hL: digitCount x ≤ size): idTerms copiesWeight size x = (Nat.keepIf x (repeats x)).toInt :=
  let m := blockCount x
  let hc: m ≤ Succ (size - 1) := omega [blockCountLe x]
  calc idTerms copiesWeight size x
    _ = x.toInt * divisorWeights copiesWeight m (size - 1) := idTermsDivisors copiesWeight size x hL
    _ = x.toInt * divisorWeights copiesWeight m (m - 1) := rewrite divisorWeightsAll copiesWeight m (blockCountPos x) (size - 1) hc
    _ = x.toInt * (Bool.toNat (Nat.leq 2 m)).toInt := rewrite weightsOne m (blockCountPos x)
    _ = (x * Bool.toNat (Nat.leq 2 m)).toInt := Eq.sym (Int.toIntMul x (Bool.toNat (Nat.leq 2 m)))
    _ = (Nat.keepIf x (repeats x)).toInt
      := Eq.cong Nat.toInt (Eq.trans (Nat.mulToNat x (Nat.leq 2 m)) (Eq.cong (Nat.keepIf x) (Eq.sym (repeatsBlocks x))))

-- (6) Swapping the sums ------------------------------------------------------

-- A term with more digits than `to` is 0 anyway.
theorem keptTerm (w: Nat → Int) (r: Range) (k: Nat) (hk: 1 ≤ k) (n: Nat) (hn: 2 ≤ n):
    (if Nat.leq (k * n) (List.length (Nat.digits r.to)) then w n * (RepetitionTemplate.sumIn { blockLength = k, copies = n } r).toInt else 0) = w n * (RepetitionTemplate.sumIn { blockLength = k, copies = n } r).toInt :=
  match h: Nat.leq (k * n) (List.length (Nat.digits r.to)) with
    | True => rfl
    | False => rewrite repeatedZero r k hk n hn h in ring

-- The program's sum over the templates, under weights w for the copies, as a
-- grid: every block length k up to the digits of `to` and every number of
-- copies n from 2, the templates that don't fit counting 0.
def weighted (w: Nat → Int) (r: Range): Int :=
  let size := List.length (Nat.digits r.to)
  List.rangeFrom size 1 |> .sumBy (k => List.rangeFrom (size - 1) 2 |> .sumBy (n => if Nat.leq (k * n) size then w n * (RepetitionTemplate.sumIn { blockLength = k, copies = n } r).toInt else 0))

theorem sumOfIdsWrittenRepeatedlyGrid (r: Range): sumOfIdsWrittenRepeatedly r = weighted copiesWeight r :=
  templatesSum r (template => copiesWeight template.copies * (RepetitionTemplate.sumIn template r).toInt)

-- One term of `weighted`, as a sum over the ids of the range.
theorem termIds (w: Nat → Int) (r: Range) (k: Nat) (hk: 1 ≤ k) (n: Nat) (hn: 2 ≤ n):
    (if Nat.leq (k * n) (List.length (Nat.digits r.to)) then w n * (RepetitionTemplate.sumIn { blockLength = k, copies = n } r).toInt else 0)
      = List.sumBy r.ids (x => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) :=
  calc (if Nat.leq (k * n) (List.length (Nat.digits r.to)) then w n * (RepetitionTemplate.sumIn { blockLength = k, copies = n } r).toInt else 0)
    _ = w n * (RepetitionTemplate.sumIn { blockLength = k, copies = n } r).toInt := keptTerm w r k hk n hn
    _ = w n * (List.sumBy r.ids (x => Nat.keepIf x (writtenAs (Nat.digits x) k n))).toInt := rewrite repeatedIds r k hk n hn
    _ = w n * List.sumBy r.ids (x => (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt)
      := rewrite Int.toIntSumBy (x => Nat.keepIf x (writtenAs (Nat.digits x) k n)) r.ids
    _ = List.sumBy r.ids (x => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt)
      := Eq.sym (Int.sumByMulLeft (w n) (x => (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt) r.ids)

-- A block written n times with more digits than `to` adds nothing.
theorem repeatedZero (r: Range) (k: Nat) (hk: 1 ≤ k) (n: Nat) (hn: 2 ≤ n) (h: Nat.leq (k * n) (List.length (Nat.digits r.to)) = False): RepetitionTemplate.sumIn { blockLength = k, copies = n } r = 0 :=
  Eq.trans (repeatedIds r k hk n hn)
    (List.sumRangeNone (x => writtenAs (Nat.digits x) k n) (x => x) r.size r.from
      (x x1 x2 =>
        match t: writtenAs (Nat.digits x) k n with
          | True =>
            omega [repCount x k n hn t, idsBelow r x x1 x2]
          | False => rfl))

-- One range under weights w, id by id.
theorem weightedIds (w: Nat → Int) (r: Range): weighted w r = List.sumBy r.ids (x => idTerms w (List.length (Nat.digits r.to)) x) :=
  let size := List.length (Nat.digits r.to)
  calc weighted w r
    _ = List.sumBy (List.rangeFrom size 1) (k => List.sumBy (List.rangeFrom (size - 1) 2) (n => List.sumBy r.ids (x => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt)))
      := rewrite termIds w r
    _ = List.sumBy (List.rangeFrom size 1) (k => List.sumBy r.ids (x => List.sumBy (List.rangeFrom (size - 1) 2) (n => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt)))
      := rewrite List.sumBySwap [c := Int] r.ids (List.rangeFrom (size - 1) 2) _
    _ = List.sumBy r.ids (x => idTerms w size x)
      := List.sumBySwap r.ids (List.rangeFrom size 1) (k x => List.sumBy (List.rangeFrom (size - 1) 2) (n => w n * (Nat.keepIf x (writtenAs (Nat.digits x) k n)).toInt))

-- One range: the signed total is the puzzle's sum, embedded.
theorem rangeWeighted (r: Range): weighted copiesWeight r = (List.sum (List.filter r.ids repeats)).toInt :=
  let size := List.length (Nat.digits r.to)
  calc weighted copiesWeight r
    _ = List.sumBy r.ids (x => idTerms copiesWeight size x) := weightedIds copiesWeight r
    _ = List.sumBy r.ids (x => (Nat.keepIf x (repeats x)).toInt)
      := rewrite idWeight size _ (idsBelow r _ _ _)
    _ = (List.sumBy r.ids (x => Nat.keepIf x (repeats x))).toInt := Eq.sym (Int.toIntSumBy (x => Nat.keepIf x (repeats x)) r.ids)
    _ = (List.sum (List.filter r.ids repeats)).toInt := Eq.cong Nat.toInt (Eq.sym (List.sumFilter r.ids repeats))

-- Part 2 is right -------------------------------------------------------------

-- Part 2 is the sum of the ids, in all the ranges, whose digits are some
-- block written two or more times. For every input. The signed total over
-- the ranges is the natural answer, embedded; that is what makes the
-- conversion back with `Int.toNat` right.
theorem part2Correct (ranges: List Range): solvePart2 ranges = part2Spec ranges :=
  calc solvePart2 ranges
    _ = Int.toNat (List.sumBy ranges (r => (List.sum (List.filter (Range.ids r) repeats)).toInt))
      := rewrite sumOfIdsWrittenRepeatedlyGrid _, rangeWeighted _
    _ = Int.toNat (part2Spec ranges).toInt
      := Eq.cong Int.toNat (Eq.sym (Int.toIntSumBy (r => List.sum (List.filter (Range.ids r) repeats)) ranges))
    _ = part2Spec ranges := Int.toNatToInt (part2Spec ranges)
