-- Day 3, proved: the greedy `Bank.best` is the largest k-digit number that can
-- be picked from a bank, in order, for any k and any bank. Kept apart from
-- the program, so `stitchwort run Aoc.Year2025.Day03.main` doesn't check it.

namespace Aoc.Year2025.Day03.Proofs
import Aoc.Year2025.Day03 (..)
import Aoc.Year2025.Day03.Spec (..)
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
theorem finDigits: (ds: List Battery) → Nat.Digits (List.map ds Fin.toNat)
  | Nil => Trivial
  | Cons d ds => Both (Fin.toNatLt d) (finDigits ds)

theorem mapLength (s: List Battery) (r: List Battery) (hl: s.length = r.length):
    List.length (List.map s Fin.toNat) = List.length (List.map r Fin.toNat) :=
  rewrite List.lengthMap s Fin.toNat, List.lengthMap r Fin.toNat in hl

-- Equal-length numbers: a smaller first digit gives a smaller number.
theorem joltageOfHeadLess (y: Battery) (t: Battery) (s: List Battery) (r: List Battery) (hl: s.length = r.length)
    (h: y.toNat < t.toNat): joltageOf (Cons y s) ≤ joltageOf (Cons t r) :=
  Nat.fromDigitsHeadLess y.toNat t.toNat (List.map s Fin.toNat) (List.map r Fin.toNat) (mapLength s r hl) (finDigits s) h

-- Equal-length numbers with the same first digit: the rest decides.
theorem joltageOfConsLe (c: Battery) (s: List Battery) (r: List Battery) (hl: s.length = r.length)
    (h: joltageOf s ≤ joltageOf r): joltageOf (Cons c s) ≤ joltageOf (Cons c r) :=
  Nat.fromDigitsConsLe c.toNat (List.map s Fin.toNat) (List.map r Fin.toNat) (mapLength s r hl) h

-- What `pick` returns.
theorem pickGe: (w: Nat) → (xs: Bank) → (c: Battery) → (after: Bank) → c.toNat ≤ Fin.toNat (Pair.fst (Bank.best.pick w xs c after))
  | Zero, xs, c, after => omega
  | Succ w, Nil, c, after => omega
  | Succ w, Cons x more, c, after =>
    match e: c < x with
      | True => omega [pickGe w more x more]
      | False => pickGe w more c after

theorem pickLen (k: Nat): (w: Nat) → (xs: Bank) → (c: Battery) → (after: Bank) →
    k + w ≤ xs.length → k ≤ after.length → k ≤ List.length (Pair.snd (Bank.best.pick w xs c after))
  | Zero, xs, c, after, h1, h2 => h2
  | Succ w, Nil, c, after, h1, h2 => h2
  | Succ w, Cons x more, c, after, h1, h2 =>
    match e: c < x with
      | True => pickLen k w more x more omega omega
      | False => pickLen k w more c after omega h2

-- If the candidate followed by `after`, and what is left to scan, are taken in
-- order from `t`, so is pick's digit followed by what comes after it.
theorem pickSub (t: Bank): (w: Nat) → (xs: Bank) → (c: Battery) → (after: Bank) →
    xs.Subsequence t → List.Subsequence (Cons c after) t →
    List.Subsequence (Cons (Pair.fst (Bank.best.pick w xs c after)) (Pair.snd (Bank.best.pick w xs c after))) t
  | Zero, xs, c, after, hx, hc => hc
  | Succ w, Nil, c, after, hx, hc => hc
  | Succ w, Cons x more, c, after, hx, hc =>
    match e: c < x with
      | True => pickSub t w more x more (List.subsequenceTail x more t hx) hx
      | False => pickSub t w more c after (List.subsequenceTail x more t hx) hc

-- 1. `best k bank` is a subsequence of `bank`.
theorem bestSub: (k: Nat) → (bank: Bank) → List.Subsequence (bank.best k) bank
  | Zero, bank => Trivial
  | Succ k, Nil => Trivial
  | Succ k, Cons d rest =>
    let p := Bank.best.pick (rest.length - k) rest d rest
    List.subsequenceTrans (Cons p.fst (Bank.best p.snd k)) (Cons p.fst p.snd) (Cons d rest)
      (Inl (Both rfl (bestSub k p.snd)))
      (pickSub (Cons d rest) (rest.length - k) rest d rest (List.subsequenceCons d rest rest (List.subsequenceRefl rest)) (List.subsequenceRefl (Cons d rest)))

theorem bestLengthStep (k: Nat) (d: Battery) (rest: Bank)
    (ih: (a: Bank) → List.length (a.best k) = Nat.min k a.length):
      Succ (List.length (Bank.best (Pair.snd (Bank.best.pick (rest.length - k) rest d rest)) k))
        = Nat.min (Succ k) (Succ rest.length) :=
  match e: Nat.leq k rest.length with
    | True =>
      rewrite ih (Pair.snd (Bank.best.pick (rest.length - k) rest d rest)),
        (omega [pickLen k (rest.length - k) rest d rest omega e]:
          Nat.min k (List.length (Pair.snd (Bank.best.pick (rest.length - k) rest d rest))) = k)
    | False =>
      rewrite ih (Pair.snd (Bank.best.pick (rest.length - k) rest d rest)),
        (omega: rest.length - k = 0),
        (omega: Nat.min k rest.length = rest.length)

-- 2. `best k bank` has k digits, or all of them if there are fewer.
theorem bestLength: (k: Nat) → (bank: Bank) → List.length (bank.best k) = Nat.min k bank.length
  | Zero, bank => rfl
  | Succ k, Nil => rfl
  | Succ k, Cons d rest => bestLengthStep k d rest (a => bestLength k a)

-- 3. No k digits of `bank`, in order, make a larger number than `best k bank`.

-- What `best k` is claimed to do: beat every k digits taken from `l`.
def BestBelow (k: Nat): Prop :=
  (l: Bank) → (s: Bank) → s.Subsequence l → s.length = k → joltageOf s ≤ joltageOf (l.best k)

-- The choices `pick` has seen so far: `y` followed by `s` is either the
-- current candidate `c` followed by digits from `after`, or a digit within
-- the next `w` of `xs` followed by digits from after it.
def Candidate (k: Nat) (w: Nat) (xs: Bank) (c: Battery) (after: Bank) (y: Battery) (s: Bank): Prop :=
  (y = c ∧ s.Subsequence after) ∨ (List.Subsequence (Cons y s) xs ∧ xs.length ≤ w + k)

-- `pick`'s choice, followed by `best k` of what comes after it, beats them all.
def PickBeats (k: Nat) (w: Nat) (xs: Bank) (c: Battery) (after: Bank): Prop :=
  k + w ≤ xs.length → k ≤ after.length → xs.Subsequence after →
  (y: Battery) → (s: Bank) → s.length = k → Candidate k w xs c after y s →
    let (top, rest) := Bank.best.pick w xs c after
    joltageOf (Cons y s) ≤ joltageOf (Cons top (Bank.best rest k))

-- `best k` of what follows the pick has k digits.
theorem pickRestLength (k: Nat) (w: Nat) (more: Bank) (c: Battery) (after: Bank) (h1: k + w ≤ more.length) (h2: k ≤ after.length):
    List.length (Bank.best (Pair.snd (Bank.best.pick w more c after)) k) = k :=
  calc List.length (Bank.best (Pair.snd (Bank.best.pick w more c after)) k)
    _ = Nat.min k (List.length (Pair.snd (Bank.best.pick w more c after))) := bestLength k (Pair.snd (Bank.best.pick w more c after))
    _ = k := omega [pickLen k w more c after h1 h2]

-- A choice starting below pick's choice loses.
theorem pickBeatsSmaller (k: Nat) (w: Nat) (more: Bank) (c: Battery) (after: Bank) (h1: k + w ≤ more.length) (h2: k ≤ after.length)
    (y: Battery) (s: Bank) (hk: s.length = k) (lt: y.toNat < Fin.toNat (Pair.fst (Bank.best.pick w more c after))):
    joltageOf (Cons y s) ≤ joltageOf (Cons (Pair.fst (Bank.best.pick w more c after)) (Bank.best (Pair.snd (Bank.best.pick w more c after)) k)) :=
  joltageOfHeadLess y (Pair.fst (Bank.best.pick w more c after)) s (Bank.best (Pair.snd (Bank.best.pick w more c after)) k) (Eq.trans hk (Eq.sym (pickRestLength k w more c after h1 h2))) lt

-- With nothing left to scan, `pick` keeps `c`.
theorem pickBase (k: Nat) (ih: BestBelow k) (c: Battery) (after: Bank) (h2: k ≤ after.length)
    (y: Battery) (s: Bank) (hk: s.length = k) (e: y = c) (hs: s.Subsequence after):
    joltageOf (Cons y s) ≤ joltageOf (Cons c (after.best k)) :=
  calc joltageOf (Cons y s)
    _ = joltageOf (Cons c s) := rewrite e
    _ ≤ joltageOf (Cons c (after.best k)) := joltageOfConsLe c s (after.best k) (omega [bestLength k after]) (ih after s hs hk)

-- When `x` ties with `c`, starting from `x` is no better than from `c`, which
-- comes earlier.
theorem pickTie (k: Nat) (w: Nat) (x: Battery) (more: Bank) (c: Battery) (after: Bank)
    (rec: (c2: Battery) → (a2: Bank) → PickBeats k w more c2 a2)
    (h1: k + w ≤ more.length) (h2: k ≤ after.length) (hsa: List.Subsequence (Cons x more) after)
    (y: Battery) (s: Bank) (hk: s.length = k) (le: x.toNat ≤ c.toNat) (eyx: y = x) (hs: s.Subsequence more):
    joltageOf (Cons y s) ≤ joltageOf (Cons (Pair.fst (Bank.best.pick w more c after)) (Bank.best (Pair.snd (Bank.best.pick w more c after)) k)) :=
  match e2: x < c with
    | True =>
      pickBeatsSmaller k w more c after h1 h2 y s hk (omega [Eq.cong Fin.toNat eyx, pickGe w more c after])
    | False =>
      rec c after h1 h2 (List.subsequenceTail x more after hsa) y s hk
        (Inl (Both (Eq.trans eyx (Fin.toNatInjective x c omega))
          (List.subsequenceTrans s more after hs (List.subsequenceTail x more after hsa))))

theorem pickBestStep (k: Nat) (w: Nat) (x: Battery) (more: Bank) (c: Battery) (after: Bank)
    (rec: (c2: Battery) → (a2: Bank) → PickBeats k w more c2 a2)
    (h1: k + w ≤ more.length) (h2: k ≤ after.length) (hsa: List.Subsequence (Cons x more) after)
    (y: Battery) (s: Bank) (hk: s.length = k) (cand: Candidate k (Succ w) (Cons x more) c after y s):
      joltageOf (Cons y s) ≤ joltageOf (Cons (Pair.fst (if c < x then Bank.best.pick w more x more else Bank.best.pick w more c after))
        (Bank.best (Pair.snd (if c < x then Bank.best.pick w more x more else Bank.best.pick w more c after)) k)) :=
  match e: c < x, cand with
    | True, Inl (Both ey hs) =>
      pickBeatsSmaller k w more x more h1 omega y s hk (omega [Eq.cong Fin.toNat ey, pickGe w more x more])
    | True, Inr (Both g hlen) =>
      rec x more h1 omega (List.subsequenceRefl more) y s hk (Or.andWith hlen g)
    | False, Inl a => rec c after h1 h2 (List.subsequenceTail x more after hsa) y s hk (Inl a)
    | False, Inr (Both (Inr g) hlen) => rec c after h1 h2 (List.subsequenceTail x more after hsa) y s hk (Inr (Both g hlen))
    | False, Inr (Both (Inl (Both eyx hs)) hlen) =>
      pickTie k w x more c after rec h1 h2 hsa y s hk omega eyx hs

theorem pickBest (k: Nat) (ih: BestBelow k): (w: Nat) → (xs: Bank) → (c: Battery) → (after: Bank) → PickBeats k w xs c after
  | Zero, xs, c, after, h1, h2, hsa, y, s, hk, Inl (Both e hs) => pickBase k ih c after h2 y s hk e hs
  | Zero, xs, c, after, h1, h2, hsa, y, s, hk, Inr (Both g hlen) =>
    omega [List.subsequenceLength (Cons y s) xs g]
  | Succ w, Nil, c, after, h1, h2, hsa, y, s, hk, Inl (Both e hs) => pickBase k ih c after h2 y s hk e hs
  | Succ w, Nil, c, after, h1, h2, hsa, y, s, hk, Inr (Both g hlen) => Void.exfalso g
  | Succ w, Cons x more, c, after, h1, h2, hsa, y, s, hk, cand =>
    pickBestStep k w x more c after (pickBest k ih w more) omega h2 hsa y s hk cand

theorem bestOptimal: (k: Nat) → BestBelow k
  | Zero, bank, Nil, h, hk => rfl
  | Zero, bank, Cons y s, h, hk => omega
  | Succ k, Nil, Nil, h, hk => omega
  | Succ k, Nil, Cons y s, h, hk => Void.exfalso h
  | Succ k, Cons d rest, Nil, h, hk => omega
  | Succ k, Cons d rest, Cons y s, h, hk =>
    bestOptimalStep k d rest y s (bestOptimal k) h omega

theorem bestOptimalStep (k: Nat) (d: Battery) (rest: Bank) (y: Battery) (s: Bank) (ih: BestBelow k)
    (h: List.Subsequence (Cons y s) (Cons d rest)) (hk: s.length = k):
    joltageOf (Cons y s) ≤ joltageOf (Bank.best (Cons d rest) (Succ k)) :=
  let enough: k ≤ rest.length := omega [List.subsequenceLength (Cons y s) (Cons d rest) h]
  pickBest k ih (rest.length - k) rest d rest omega enough (List.subsequenceRefl rest) y s hk
    (Or.andWith omega h)

-- 4. Whichever k batteries you turn on, they produce no more than maxJoltage.
theorem maxJoltageIsLargest (k: Nat) (bank: Bank) (on: List Battery)
    (turnsOn: TurnsOn k bank on):
    joltageOf on ≤ maxJoltage k bank := bestOptimal k bank on turnsOn.left turnsOn.right

-- 5. The headline, in the puzzle's words. When the bank has at least k
-- batteries, `maxJoltage k bank` is the largest joltage you can get by
-- turning on exactly k of them: some k batteries of the bank, turned on in
-- order, do produce it (the ones `Bank.best bank k` picks), and no k batteries
-- of the bank produce more.
theorem maxJoltageIsMaximum (k: Nat) (bank: Bank) (enough: k ≤ bank.length):
    (TurnsOn k bank (bank.best k) ∧ joltageOf (bank.best k) = maxJoltage k bank)
      ∧ ((on: List Battery) → TurnsOn k bank on → joltageOf on ≤ maxJoltage k bank) :=
  Both
    (Both
      (Both (bestSub k bank) (omega [bestLength k bank]))
      rfl)
    (on turnsOn => maxJoltageIsLargest k bank on turnsOn)
