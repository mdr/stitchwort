-- Day 3, proved: the greedy `Bank.best` is the largest k-digit number that can
-- be picked from a bank, in order, for any k and any bank. Kept apart from
-- the program, so `stitchwort run Aoc.Day03.main` doesn't check it.

namespace Aoc.Day03.Proofs
import Aoc.Day03 (..)
import Std (Bool, Decidable, Eq, Fin, List, Nat, Or, Ordering, Pair, Void)

-- Four facts about `best k bank` (plain-words summary in docs/aoc-2025.md):
--   1. `bestSub`: it is a subsequence of `bank` (batteries taken in order).
--   2. `bestLength`: it has `min k (length bank)` digits.
--   3. `bestOptimal`: no k batteries of `bank`, taken in order, make a
--      larger joltage.
--   4. `maxJoltageIsLargest`: so no k batteries make more joltage than
--      `maxJoltage k bank`.
--   5. `maxJoltageIsMaximum`, the headline: `maxJoltage k bank` is the
--      largest joltage from turning on exactly k batteries of the bank.
-- The optimality argument: every choice starts with some digit y inside the
-- window that `pick` scans (it must leave k - 1 digits after it). If y is
-- below pick's digit, the choice loses on its first digit
-- (`Nat.fromDigitsHeadLess`). If y equals it, y is at pick's position or
-- later, since pick takes the leftmost largest, so the rest of the choice
-- comes from what follows pick's digit, where `best` (by induction on k)
-- does at least as well.

-- Digits as numbers are digits.
theorem finDigits: (ds: List Battery) -> Nat.Digits (List.map Fin.toNat ds)
  | Nil       => Trivial
  | Cons d ds => Both (Fin.toNatLt d) (finDigits ds)

theorem mapLength (s: List Battery) (r: List Battery) (hl: s.length = r.length):
  List.length (List.map Fin.toNat s) = List.length (List.map Fin.toNat r) :=
  rewrite List.lengthMap Fin.toNat s, List.lengthMap Fin.toNat r in hl

-- Equal-length numbers: a smaller first digit gives a smaller number.
theorem joltageOfHeadLess (y: Battery) (t: Battery) (s: List Battery) (r: List Battery) (hl: s.length = r.length)
  (h: y.toNat < t.toNat): joltageOf (Cons y s) <= joltageOf (Cons t r) :=
  Nat.fromDigitsHeadLess y.toNat t.toNat (List.map Fin.toNat s) (List.map Fin.toNat r) (mapLength s r hl) (finDigits s) h

-- Equal-length numbers with the same first digit: the rest decides.
theorem joltageOfConsLe (c: Battery) (s: List Battery) (r: List Battery) (hl: s.length = r.length)
  (h: joltageOf s <= joltageOf r): joltageOf (Cons c s) <= joltageOf (Cons c r) :=
  Nat.fromDigitsConsLe c.toNat (List.map Fin.toNat s) (List.map Fin.toNat r) (mapLength s r hl) h

theorem pickStep (w: Nat) (x: Battery) (more: Bank) (c: Battery) (after: Bank):
    Bank.best.pick (Succ w) (Cons x more) c after
      = (if Fin.toNat c < x.toNat then Bank.best.pick w more x more else Bank.best.pick w more c after) :=
  rfl

-- What `pick` returns.
theorem pickGe: (w: Nat) -> (xs: Bank) -> (c: Battery) -> (after: Bank) -> c.toNat <= Fin.toNat (Pair.fst (Bank.best.pick w xs c after))
  | Zero,   xs,          c, after => Nat.leRefl c.toNat
  | Succ w, Nil,         c, after => Nat.leRefl c.toNat
  | Succ w, Cons x more, c, after =>
    rewrite pickStep w x more c after in
      match e: Nat.leq (Succ c.toNat) x.toNat with
        | True  =>
          Nat.leTrans c.toNat x.toNat (Fin.toNat (Pair.fst (Bank.best.pick w more x more)))
            (Nat.lessLe c.toNat x.toNat e) (pickGe w more x more)
        | False => pickGe w more c after

theorem pickLen (k: Nat): (w: Nat) -> (xs: Bank) -> (c: Battery) -> (after: Bank) ->
    k + w <= xs.length -> k <= after.length -> k <= List.length (Pair.snd (Bank.best.pick w xs c after))
  | Zero,   xs,          c, after, h1, h2 => h2
  | Succ w, Nil,         c, after, h1, h2 => h2
  | Succ w, Cons x more, c, after, h1, h2 =>
    rewrite pickStep w x more c after in
      match e: Nat.leq (Succ c.toNat) x.toNat with
        | True  => pickLen k w more x more (Nat.addSuccLeSucc k w more.length h1) (Nat.leOfAddLe k w more.length (Nat.addSuccLeSucc k w more.length h1))
        | False => pickLen k w more c after (Nat.addSuccLeSucc k w more.length h1) h2

theorem pickSub (t: Bank): (w: Nat) -> (xs: Bank) -> (c: Battery) -> (after: Bank) ->
    ((s: Bank) -> s.Subsequence xs -> s.Subsequence t) ->
    ((s: Bank) -> s.Subsequence after -> List.Subsequence (Cons c s) t) ->
    (s: Bank) -> s.Subsequence (Pair.snd (Bank.best.pick w xs c after)) -> List.Subsequence (Cons (Pair.fst (Bank.best.pick w xs c after)) s) t
  | Zero,   xs,          c, after, hx, hc, s, h => hc s h
  | Succ w, Nil,         c, after, hx, hc, s, h => hc s h
  | Succ w, Cons x more, c, after, hx, hc, s, h =>
    rewrite pickStep w x more c after in
      match e: Nat.leq (Succ c.toNat) x.toNat with
        | True  => pickSub t w more x more (s2 g2 => hx s2 (List.subsequenceCons x s2 more g2)) (s2 g2 => hx (Cons x s2) (Inl (Both rfl g2))) s h
        | False => pickSub t w more c after (s2 g2 => hx s2 (List.subsequenceCons x s2 more g2)) hc s h

-- 1. `best k bank` is a subsequence of `bank`.
theorem bestSub: (k: Nat) -> (bank: Bank) -> List.Subsequence (bank.best k) bank
  | Zero,   bank        => Trivial
  | Succ k, Nil         => Trivial
  | Succ k, Cons d rest =>
    pickSub (Cons d rest) (rest.length - k) rest d rest (s h => List.subsequenceCons d s rest h) (s h => Inl (Both rfl h))
      (Bank.best k (Pair.snd (Bank.best.pick (rest.length - k) rest d rest))) (bestSub k (Pair.snd (Bank.best.pick (rest.length - k) rest d rest)))

theorem bestLengthStep (k: Nat) (d: Battery) (rest: Bank)
  (ih: (a: Bank) -> List.length (a.best k) = Nat.min k a.length):
    Succ (List.length (Bank.best k (Pair.snd (Bank.best.pick (rest.length - k) rest d rest))))
      = Bool.ifThenElse (Nat.leq k rest.length) (u => Succ k) (u => Succ rest.length) :=
  match e: Nat.leq k rest.length with
    | True =>
      rewrite ih (Pair.snd (Bank.best.pick (rest.length - k) rest d rest)),
          Nat.minLeft k (List.length (Pair.snd (Bank.best.pick (rest.length - k) rest d rest)))
            (pickLen k (rest.length - k) rest d rest (Nat.addSubLe k rest.length e) e)
    | False =>
      rewrite ih (Pair.snd (Bank.best.pick (rest.length - k) rest d rest)),
          Nat.subEqZero rest.length k (Nat.lessLe rest.length k (Nat.leqFalse k rest.length e)),
          Nat.minRight k rest.length e

-- 2. `best k bank` has k digits, or all of them if there are fewer.
theorem bestLength: (k: Nat) -> (bank: Bank) -> List.length (bank.best k) = Nat.min k bank.length
  | Zero,   bank        => rfl
  | Succ k, Nil         => rfl
  | Succ k, Cons d rest => bestLengthStep k d rest (a => bestLength k a)

-- 3. No k digits of `bank`, in order, make a larger number than `best k bank`.

-- What `best k` is claimed to do: beat every k digits taken from `l`.
def BestBelow (k: Nat): Prop :=
  (l: Bank) -> (s: Bank) -> s.Subsequence l -> s.length = k -> joltageOf s <= joltageOf (l.best k)

-- The choices `pick` has seen so far: `y` followed by `s` is either the
-- current candidate `c` followed by digits from `after`, or a digit within
-- the next `w` of `xs` followed by digits from after it.
def Candidate (k: Nat) (w: Nat) (xs: Bank) (c: Battery) (after: Bank) (y: Battery) (s: Bank): Prop :=
  (y = c && s.Subsequence after) || (List.Subsequence (Cons y s) xs && xs.length <= w + k)

-- `pick`'s choice, followed by `best k` of what comes after it, beats them all.
def PickBeats (k: Nat) (w: Nat) (xs: Bank) (c: Battery) (after: Bank): Prop :=
  k + w <= xs.length -> k <= after.length -> ((s: Bank) -> s.Subsequence xs -> s.Subsequence after) ->
  (y: Battery) -> (s: Bank) -> s.length = k -> Candidate k w xs c after y s ->
  joltageOf (Cons y s) <= joltageOf (Cons (Pair.fst (Bank.best.pick w xs c after)) (Bank.best k (Pair.snd (Bank.best.pick w xs c after))))

-- `best k` of what follows the pick has k digits.
theorem pickRestLength (k: Nat) (w: Nat) (more: Bank) (c: Battery) (after: Bank) (h1: k + w <= more.length) (h2: k <= after.length):
  List.length (Bank.best k (Pair.snd (Bank.best.pick w more c after))) = k :=
  calc List.length (Bank.best k (Pair.snd (Bank.best.pick w more c after)))
    _ = Nat.min k (List.length (Pair.snd (Bank.best.pick w more c after))) := bestLength k (Pair.snd (Bank.best.pick w more c after))
    _ = k := Nat.minLeft k (List.length (Pair.snd (Bank.best.pick w more c after))) (pickLen k w more c after h1 h2)

-- A choice starting below pick's choice loses.
theorem pickBeatsSmaller (k: Nat) (w: Nat) (more: Bank) (c: Battery) (after: Bank) (h1: k + w <= more.length) (h2: k <= after.length)
  (y: Battery) (s: Bank) (hk: s.length = k) (lt: y.toNat < Fin.toNat (Pair.fst (Bank.best.pick w more c after))):
  joltageOf (Cons y s) <= joltageOf (Cons (Pair.fst (Bank.best.pick w more c after)) (Bank.best k (Pair.snd (Bank.best.pick w more c after)))) :=
  joltageOfHeadLess y (Pair.fst (Bank.best.pick w more c after)) s (Bank.best k (Pair.snd (Bank.best.pick w more c after))) (Eq.trans hk (Eq.sym (pickRestLength k w more c after h1 h2))) lt

-- With nothing left to scan, `pick` keeps `c`.
theorem pickBase (k: Nat) (ih: BestBelow k) (c: Battery) (after: Bank) (h2: k <= after.length)
  (y: Battery) (s: Bank) (hk: s.length = k) (e: y = c) (hs: s.Subsequence after):
  joltageOf (Cons y s) <= joltageOf (Cons c (after.best k)) :=
  calc joltageOf (Cons y s)
    _ = joltageOf (Cons c s) := Eq.cong (z => joltageOf (Cons z s)) e
    _ <= joltageOf (Cons c (after.best k)) := joltageOfConsLe c s (after.best k) (Eq.trans hk (Eq.sym (Eq.trans (bestLength k after) (Nat.minLeft k after.length h2)))) (ih after s hs hk)

-- When `x` ties with `c`, starting from `x` is no better than from `c`, which
-- comes earlier.
theorem pickTie (k: Nat) (w: Nat) (x: Battery) (more: Bank) (c: Battery) (after: Bank)
  (rec: (c2: Battery) -> (a2: Bank) -> PickBeats k w more c2 a2)
  (h1: k + w <= more.length) (h2: k <= after.length) (hsa: (s: Bank) -> s.Subsequence (Cons x more) -> s.Subsequence after)
  (y: Battery) (s: Bank) (hk: s.length = k) (le: x.toNat <= c.toNat) (eyx: y = x) (hs: s.Subsequence more):
  joltageOf (Cons y s) <= joltageOf (Cons (Pair.fst (Bank.best.pick w more c after)) (Bank.best k (Pair.snd (Bank.best.pick w more c after)))) :=
  match e2: Nat.leq (Succ x.toNat) c.toNat with
    | True =>
      pickBeatsSmaller k w more c after h1 h2 y s hk
        (Nat.ltCongLeft x.toNat y.toNat (Fin.toNat (Pair.fst (Bank.best.pick w more c after))) (Eq.sym (Eq.cong Fin.toNat eyx))
          (Nat.leTrans (Succ x.toNat) c.toNat (Fin.toNat (Pair.fst (Bank.best.pick w more c after))) e2 (pickGe w more c after)))
    | False =>
      rec c after h1 h2 (t h => hsa t (List.subsequenceCons x t more h)) y s hk
        (Inl (Both (Eq.trans eyx (Fin.toNatInjective x c (Nat.leAntisym x.toNat c.toNat le (Nat.leqFalse (Succ x.toNat) c.toNat e2))))
                   (hsa s (List.subsequenceCons x s more hs))))

theorem pickBestStep (k: Nat) (w: Nat) (x: Battery) (more: Bank) (c: Battery) (after: Bank)
  (rec: (c2: Battery) -> (a2: Bank) -> PickBeats k w more c2 a2)
  (h1: k + w <= more.length) (h2: k <= after.length) (hsa: (s: Bank) -> s.Subsequence (Cons x more) -> s.Subsequence after)
  (y: Battery) (s: Bank) (hk: s.length = k) (cand: Candidate k (Succ w) (Cons x more) c after y s):
    joltageOf (Cons y s) <= joltageOf (Cons (Pair.fst (if Fin.toNat c < x.toNat then Bank.best.pick w more x more else Bank.best.pick w more c after))
      (Bank.best k (Pair.snd (if Fin.toNat c < x.toNat then Bank.best.pick w more x more else Bank.best.pick w more c after)))) :=
  match e: Nat.leq (Succ c.toNat) x.toNat, cand with
    | True, Inl (Both ey hs) =>
      pickBeatsSmaller k w more x more h1 (Nat.leOfAddLe k w more.length h1) y s hk
        (Nat.ltCongLeft c.toNat y.toNat (Fin.toNat (Pair.fst (Bank.best.pick w more x more))) (Eq.sym (Eq.cong Fin.toNat ey))
          (Nat.leTrans (Succ c.toNat) x.toNat (Fin.toNat (Pair.fst (Bank.best.pick w more x more))) e (pickGe w more x more)))
    | True, Inr (Both g hlen) =>
      rec x more h1 (Nat.leOfAddLe k w more.length h1) (t h => h) y s hk (Or.andWith hlen g)
    | False, Inl a => rec c after h1 h2 (t h => hsa t (List.subsequenceCons x t more h)) y s hk (Inl a)
    | False, Inr (Both (Inr g) hlen) => rec c after h1 h2 (t h => hsa t (List.subsequenceCons x t more h)) y s hk (Inr (Both g hlen))
    | False, Inr (Both (Inl (Both eyx hs)) hlen) =>
      pickTie k w x more c after rec h1 h2 hsa y s hk (Nat.leqFalse (Succ c.toNat) x.toNat e) eyx hs

theorem pickBest (k: Nat) (ih: BestBelow k): (w: Nat) -> (xs: Bank) -> (c: Battery) -> (after: Bank) -> PickBeats k w xs c after
  | Zero, xs, c, after, h1, h2, hsa, y, s, hk, Inl (Both e hs) => pickBase k ih c after h2 y s hk e hs
  | Zero, xs, c, after, h1, h2, hsa, y, s, hk, Inr (Both g hlen) =>
    Void.exfalso (Nat.lessIrrefl k (Nat.ltCongLeft s.length k k hk
      (Nat.leTrans (Succ s.length) xs.length k (List.subsequenceLength (Cons y s) xs g) hlen)))
  | Succ w, Nil, c, after, h1, h2, hsa, y, s, hk, Inl (Both e hs) => pickBase k ih c after h2 y s hk e hs
  | Succ w, Nil, c, after, h1, h2, hsa, y, s, hk, Inr (Both g hlen) => Void.exfalso g
  | Succ w, Cons x more, c, after, h1, h2, hsa, y, s, hk, cand =>
    rewrite pickStep w x more c after in
      pickBestStep k w x more c after
        (c2 a2 g1 g2 g3 y2 s2 g5 g6 => pickBest k ih w more c2 a2 g1 g2 g3 y2 s2 g5 g6)
        (Nat.addSuccLeSucc k w more.length h1) h2 hsa y s hk cand

theorem bestOptimal: (k: Nat) -> BestBelow k
  | Zero,   bank,        Nil,      h, hk => rfl
  | Zero,   bank,        Cons y s, h, hk => Void.exfalso (Nat.succNotZero s.length hk)
  | Succ k, Nil,         Nil,      h, hk => Void.exfalso (Nat.zeroNotSucc k hk)
  | Succ k, Nil,         Cons y s, h, hk => Void.exfalso h
  | Succ k, Cons d rest, Nil,      h, hk => Void.exfalso (Nat.zeroNotSucc k hk)
  | Succ k, Cons d rest, Cons y s, h, hk =>
    bestOptimalStep k d rest y s (l t g gk => bestOptimal k l t g gk) h (Nat.succInjective s.length k hk)

theorem bestOptimalStep (k: Nat) (d: Battery) (rest: Bank) (y: Battery) (s: Bank) (ih: BestBelow k)
  (h: List.Subsequence (Cons y s) (Cons d rest)) (hk: s.length = k):
  joltageOf (Cons y s) <= joltageOf (Bank.best (Succ k) (Cons d rest)) :=
  pickBest k ih (rest.length - k) rest d rest
    (Nat.addSubLe k rest.length (Nat.leCongLeft s.length k rest.length hk (List.subsequenceLength (Cons y s) (Cons d rest) h)))
    (Nat.leCongLeft s.length k rest.length hk (List.subsequenceLength (Cons y s) (Cons d rest) h))
    (t g => g) y s hk
    (Or.andWith (Nat.leSubAdd k rest.length (Nat.leCongLeft s.length k rest.length hk (List.subsequenceLength (Cons y s) (Cons d rest) h))) h)

-- `on` is k of the bank's batteries, turned on in the bank's order.
def TurnsOn (k: Nat) (bank: Bank) (on: List Battery): Prop :=
  on.Subsequence bank && on.length = k

-- 4. Whichever k batteries you turn on, they produce no more than maxJoltage.
theorem maxJoltageIsLargest (k: Nat) (bank: Bank) (on: List Battery)
    (turnsOn: TurnsOn k bank on):
  joltageOf on <= maxJoltage k bank := bestOptimal k bank on turnsOn.left turnsOn.right

-- 5. The headline, in the puzzle's words. When the bank has at least k
-- batteries, `maxJoltage k bank` is the largest joltage you can get by
-- turning on exactly k of them: some k batteries of the bank, turned on in
-- order, do produce it (the ones `Bank.best k bank` picks), and no k batteries
-- of the bank produce more.
theorem maxJoltageIsMaximum (k: Nat) (bank: Bank) (enough: k <= bank.length):
  (TurnsOn k bank (bank.best k) && joltageOf (bank.best k) = maxJoltage k bank)
      && ((on: List Battery) -> TurnsOn k bank on -> joltageOf on <= maxJoltage k bank) :=
  Both
    (Both
      (Both (bestSub k bank) (Eq.trans (bestLength k bank) (Nat.minLeft k bank.length enough)))
      rfl)
    (on turnsOn => maxJoltageIsLargest k bank on turnsOn)
