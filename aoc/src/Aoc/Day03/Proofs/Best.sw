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
--      larger number.
--   4. `bestIsLargest`: so no k batteries make more joltage than
--      `joltage k bank`.
-- The optimality argument: every choice starts with some digit y inside the
-- window that `pick` scans (it must leave k - 1 digits after it). If y is
-- below pick's digit, the choice loses on its first digit
-- (`Nat.fromDigitsHeadLess`). If y equals it, y is at pick's position or
-- later, since pick takes the leftmost largest, so the rest of the choice
-- comes from what follows pick's digit, where `best` (by induction on k)
-- does at least as well.

-- The number some digits make, read as `joltage` reads them.
def number (ds: List (Fin 10)): Nat := Nat.fromDigits (List.map Fin.toNat ds)

-- Digits as numbers are digits.
theorem finDigits: (ds: List (Fin 10)) -> Nat.Digits (List.map Fin.toNat ds)
  | Nil       => Trivial
  | Cons d ds => Both (Fin.toNatLt d) (finDigits ds)

theorem mapLength (s: List (Fin 10)) (r: List (Fin 10)) (hl: List.length s = List.length r):
  List.length (List.map Fin.toNat s) = List.length (List.map Fin.toNat r) :=
  rewrite List.lengthMap Fin.toNat s, List.lengthMap Fin.toNat r in hl

-- Equal-length numbers: a smaller first digit gives a smaller number.
theorem numberHeadLess (y: Fin 10) (t: Fin 10) (s: List (Fin 10)) (r: List (Fin 10)) (hl: List.length s = List.length r)
  (h: Fin.toNat y < Fin.toNat t): number (Cons y s) <= number (Cons t r) :=
  Nat.fromDigitsHeadLess (Fin.toNat y) (Fin.toNat t) (List.map Fin.toNat s) (List.map Fin.toNat r) (mapLength s r hl) (finDigits s) h

-- Equal-length numbers with the same first digit: the rest decides.
theorem numberConsLe (c: Fin 10) (s: List (Fin 10)) (r: List (Fin 10)) (hl: List.length s = List.length r)
  (h: number s <= number r): number (Cons c s) <= number (Cons c r) :=
  Nat.fromDigitsConsLe (Fin.toNat c) (List.map Fin.toNat s) (List.map Fin.toNat r) (mapLength s r hl) h

theorem pickStep (w: Nat) (x: Fin 10) (more: Bank) (c: Fin 10) (after: Bank):
    Bank.best.pick (Succ w) (Cons x more) c after
      = (if Fin.toNat c < Fin.toNat x then Bank.best.pick w more x more else Bank.best.pick w more c after) :=
  rfl

-- What `pick` returns.
theorem pickGe: (w: Nat) -> (xs: Bank) -> (c: Fin 10) -> (after: Bank) -> Fin.toNat c <= Fin.toNat (Pair.fst (Bank.best.pick w xs c after))
  | Zero,   xs,          c, after => Nat.leRefl (Fin.toNat c)
  | Succ w, Nil,         c, after => Nat.leRefl (Fin.toNat c)
  | Succ w, Cons x more, c, after =>
    rewrite pickStep w x more c after in
      match e: Nat.leq (Succ (Fin.toNat c)) (Fin.toNat x) with
        | True  =>
          Nat.leTrans (Fin.toNat c) (Fin.toNat x) (Fin.toNat (Pair.fst (Bank.best.pick w more x more)))
            (Nat.lessLe (Fin.toNat c) (Fin.toNat x) e) (pickGe w more x more)
        | False => pickGe w more c after

theorem pickLen (k: Nat): (w: Nat) -> (xs: Bank) -> (c: Fin 10) -> (after: Bank) ->
    k + w <= List.length xs -> k <= List.length after -> k <= List.length (Pair.snd (Bank.best.pick w xs c after))
  | Zero,   xs,          c, after, h1, h2 => h2
  | Succ w, Nil,         c, after, h1, h2 => h2
  | Succ w, Cons x more, c, after, h1, h2 =>
    rewrite pickStep w x more c after in
      match e: Nat.leq (Succ (Fin.toNat c)) (Fin.toNat x) with
        | True  => pickLen k w more x more (Nat.addSuccLeSucc k w (List.length more) h1) (Nat.leOfAddLe k w (List.length more) (Nat.addSuccLeSucc k w (List.length more) h1))
        | False => pickLen k w more c after (Nat.addSuccLeSucc k w (List.length more) h1) h2

theorem pickSub (t: Bank): (w: Nat) -> (xs: Bank) -> (c: Fin 10) -> (after: Bank) ->
    ((s: Bank) -> List.Subsequence s xs -> List.Subsequence s t) ->
    ((s: Bank) -> List.Subsequence s after -> List.Subsequence (Cons c s) t) ->
    (s: Bank) -> List.Subsequence s (Pair.snd (Bank.best.pick w xs c after)) -> List.Subsequence (Cons (Pair.fst (Bank.best.pick w xs c after)) s) t
  | Zero,   xs,          c, after, hx, hc, s, h => hc s h
  | Succ w, Nil,         c, after, hx, hc, s, h => hc s h
  | Succ w, Cons x more, c, after, hx, hc, s, h =>
    rewrite pickStep w x more c after in
      pickSubStep t w x more c after hx hc (Bool.decTrue (Nat.leq (Succ (Fin.toNat c)) (Fin.toNat x))) s
        (J (p q => List.Subsequence s (Pair.snd p)) h (pickStep w x more c after))

-- `pickSub` one step on, whichever way `pick` goes.
theorem pickSubStep (t: Bank) (w: Nat) (x: Fin 10) (more: Bank) (c: Fin 10) (after: Bank)
    (hx: (s: Bank) -> List.Subsequence s (Cons x more) -> List.Subsequence s t)
    (hc: (s: Bank) -> List.Subsequence s after -> List.Subsequence (Cons c s) t):
    (d: Decidable (Fin.toNat c < Fin.toNat x)) -> (s: Bank) ->
    List.Subsequence s (Pair.snd (Decidable.elim d (u => Bank.best.pick w more x more) (u => Bank.best.pick w more c after))) ->
    List.Subsequence (Cons (Pair.fst (Decidable.elim d (u => Bank.best.pick w more x more) (u => Bank.best.pick w more c after))) s) t
  | Yes lt, s, h => pickSub t w more x more (s2 g2 => hx s2 (List.subsequenceCons x s2 more g2)) (s2 g2 => hx (Cons x s2) (Inl (Both rfl g2))) s h
  | No ge,  s, h => pickSub t w more c after (s2 g2 => hx s2 (List.subsequenceCons x s2 more g2)) hc s h

-- 1. `best k bank` is a subsequence of `bank`.
theorem bestSub: (k: Nat) -> (bank: Bank) -> List.Subsequence (Bank.best k bank) bank
  | Zero,   bank        => Trivial
  | Succ k, Nil         => Trivial
  | Succ k, Cons d rest =>
    pickSub (Cons d rest) (List.length rest - k) rest d rest (s h => List.subsequenceCons d s rest h) (s h => Inl (Both rfl h))
      (Bank.best k (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest))) (bestSub k (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest)))

theorem bestLengthStep (k: Nat) (d: Fin 10) (rest: Bank)
  (ih: (a: Bank) -> List.length (Bank.best k a) = Nat.min k (List.length a)):
    Succ (List.length (Bank.best k (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest))))
      = Bool.ifThenElse (Nat.leq k (List.length rest)) (u => Succ k) (u => Succ (List.length rest)) :=
  match e: Nat.leq k (List.length rest) with
    | True =>
      rewrite ih (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest)),
          Nat.minLeft k (List.length (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest)))
            (pickLen k (List.length rest - k) rest d rest (Nat.addSubLe k (List.length rest) e) e)
    | False =>
      rewrite ih (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest)),
          Nat.subEqZero (List.length rest) k (Nat.lessLe (List.length rest) k (Nat.leqFalse k (List.length rest) e)),
          Nat.minRight k (List.length rest) e

-- 2. `best k bank` has k digits, or all of them if there are fewer.
theorem bestLength: (k: Nat) -> (bank: Bank) -> List.length (Bank.best k bank) = Nat.min k (List.length bank)
  | Zero,   bank        => rfl
  | Succ k, Nil         => rfl
  | Succ k, Cons d rest => bestLengthStep k d rest (a => bestLength k a)

-- 3. No k digits of `bank`, in order, make a larger number than `best k bank`.

-- What `best k` is claimed to do: beat every k digits taken from `l`.
def BestBelow (k: Nat): Prop :=
  (l: Bank) -> (s: Bank) -> List.Subsequence s l -> List.length s = k -> number s <= number (Bank.best k l)

-- The choices `pick` has seen so far: `y` followed by `s` is either the
-- current candidate `c` followed by digits from `after`, or a digit within
-- the next `w` of `xs` followed by digits from after it.
def Candidate (k: Nat) (w: Nat) (xs: Bank) (c: Fin 10) (after: Bank) (y: Fin 10) (s: Bank): Prop :=
  Or (And (y = c) (List.Subsequence s after)) (And (List.Subsequence (Cons y s) xs) (List.length xs <= w + k))

-- `pick`'s choice, followed by `best k` of what comes after it, beats them all.
def PickBeats (k: Nat) (w: Nat) (xs: Bank) (c: Fin 10) (after: Bank): Prop :=
  k + w <= List.length xs -> k <= List.length after -> ((s: Bank) -> List.Subsequence s xs -> List.Subsequence s after) ->
  (y: Fin 10) -> (s: Bank) -> List.length s = k -> Candidate k w xs c after y s ->
  number (Cons y s) <= number (Cons (Pair.fst (Bank.best.pick w xs c after)) (Bank.best k (Pair.snd (Bank.best.pick w xs c after))))

-- `best k` of what follows the pick has k digits.
theorem pickRestLength (k: Nat) (w: Nat) (more: Bank) (c: Fin 10) (after: Bank) (h1: k + w <= List.length more) (h2: k <= List.length after):
  List.length (Bank.best k (Pair.snd (Bank.best.pick w more c after))) = k :=
  calc List.length (Bank.best k (Pair.snd (Bank.best.pick w more c after)))
    _ = Nat.min k (List.length (Pair.snd (Bank.best.pick w more c after))) := bestLength k (Pair.snd (Bank.best.pick w more c after))
    _ = k := Nat.minLeft k (List.length (Pair.snd (Bank.best.pick w more c after))) (pickLen k w more c after h1 h2)

-- A choice starting below pick's choice loses.
theorem pickBeatsSmaller (k: Nat) (w: Nat) (more: Bank) (c: Fin 10) (after: Bank) (h1: k + w <= List.length more) (h2: k <= List.length after)
  (y: Fin 10) (s: Bank) (hk: List.length s = k) (lt: Fin.toNat y < Fin.toNat (Pair.fst (Bank.best.pick w more c after))):
  number (Cons y s) <= number (Cons (Pair.fst (Bank.best.pick w more c after)) (Bank.best k (Pair.snd (Bank.best.pick w more c after)))) :=
  numberHeadLess y (Pair.fst (Bank.best.pick w more c after)) s (Bank.best k (Pair.snd (Bank.best.pick w more c after))) (Eq.trans hk (Eq.sym (pickRestLength k w more c after h1 h2))) lt

-- With nothing left to scan, `pick` keeps `c`.
theorem pickBase (k: Nat) (ih: BestBelow k) (c: Fin 10) (after: Bank) (h2: k <= List.length after)
  (y: Fin 10) (s: Bank) (hk: List.length s = k) (e: y = c) (hs: List.Subsequence s after):
  number (Cons y s) <= number (Cons c (Bank.best k after)) :=
  calc number (Cons y s)
    _ = number (Cons c s) := Eq.cong (z => number (Cons z s)) e
    _ <= number (Cons c (Bank.best k after)) := numberConsLe c s (Bank.best k after) (Eq.trans hk (Eq.sym (Eq.trans (bestLength k after) (Nat.minLeft k (List.length after) h2)))) (ih after s hs hk)

-- When `x` ties with `c`, starting from `x` is no better than from `c`, which
-- comes earlier.
theorem pickTie (k: Nat) (w: Nat) (x: Fin 10) (more: Bank) (c: Fin 10) (after: Bank)
  (rec: (c2: Fin 10) -> (a2: Bank) -> PickBeats k w more c2 a2)
  (h1: k + w <= List.length more) (h2: k <= List.length after) (hsa: (s: Bank) -> List.Subsequence s (Cons x more) -> List.Subsequence s after)
  (y: Fin 10) (s: Bank) (hk: List.length s = k) (le: Fin.toNat x <= Fin.toNat c) (eyx: y = x) (hs: List.Subsequence s more):
  number (Cons y s) <= number (Cons (Pair.fst (Bank.best.pick w more c after)) (Bank.best k (Pair.snd (Bank.best.pick w more c after)))) :=
  match e2: Nat.leq (Succ (Fin.toNat x)) (Fin.toNat c) with
    | True =>
      pickBeatsSmaller k w more c after h1 h2 y s hk
        (Nat.ltCongLeft (Fin.toNat x) (Fin.toNat y) (Fin.toNat (Pair.fst (Bank.best.pick w more c after))) (Eq.sym (Eq.cong Fin.toNat eyx))
          (Nat.leTrans (Succ (Fin.toNat x)) (Fin.toNat c) (Fin.toNat (Pair.fst (Bank.best.pick w more c after))) e2 (pickGe w more c after)))
    | False =>
      rec c after h1 h2 (t h => hsa t (List.subsequenceCons x t more h)) y s hk
        (Inl (Both (Eq.trans eyx (Fin.toNatInjective x c (Nat.leAntisym (Fin.toNat x) (Fin.toNat c) le (Nat.leqFalse (Succ (Fin.toNat x)) (Fin.toNat c) e2))))
                   (hsa s (List.subsequenceCons x s more hs))))

theorem pickBestStep (k: Nat) (w: Nat) (x: Fin 10) (more: Bank) (c: Fin 10) (after: Bank)
  (rec: (c2: Fin 10) -> (a2: Bank) -> PickBeats k w more c2 a2)
  (h1: k + w <= List.length more) (h2: k <= List.length after) (hsa: (s: Bank) -> List.Subsequence s (Cons x more) -> List.Subsequence s after)
  (y: Fin 10) (s: Bank) (hk: List.length s = k) (cand: Candidate k (Succ w) (Cons x more) c after y s):
    number (Cons y s) <= number (Cons (Pair.fst (if Fin.toNat c < Fin.toNat x then Bank.best.pick w more x more else Bank.best.pick w more c after))
      (Bank.best k (Pair.snd (if Fin.toNat c < Fin.toNat x then Bank.best.pick w more x more else Bank.best.pick w more c after)))) :=
  match e: Nat.leq (Succ (Fin.toNat c)) (Fin.toNat x), cand with
    | True, Inl (Both ey hs) =>
      pickBeatsSmaller k w more x more h1 (Nat.leOfAddLe k w (List.length more) h1) y s hk
        (Nat.ltCongLeft (Fin.toNat c) (Fin.toNat y) (Fin.toNat (Pair.fst (Bank.best.pick w more x more))) (Eq.sym (Eq.cong Fin.toNat ey))
          (Nat.leTrans (Succ (Fin.toNat c)) (Fin.toNat x) (Fin.toNat (Pair.fst (Bank.best.pick w more x more))) e (pickGe w more x more)))
    | True, Inr (Both g hlen) =>
      rec x more h1 (Nat.leOfAddLe k w (List.length more) h1) (t h => h) y s hk (Or.andWith hlen g)
    | False, Inl a => rec c after h1 h2 (t h => hsa t (List.subsequenceCons x t more h)) y s hk (Inl a)
    | False, Inr (Both (Inr g) hlen) => rec c after h1 h2 (t h => hsa t (List.subsequenceCons x t more h)) y s hk (Inr (Both g hlen))
    | False, Inr (Both (Inl (Both eyx hs)) hlen) =>
      pickTie k w x more c after rec h1 h2 hsa y s hk (Nat.leqFalse (Succ (Fin.toNat c)) (Fin.toNat x) e) eyx hs

theorem pickBest (k: Nat) (ih: BestBelow k): (w: Nat) -> (xs: Bank) -> (c: Fin 10) -> (after: Bank) -> PickBeats k w xs c after
  | Zero, xs, c, after, h1, h2, hsa, y, s, hk, Inl (Both e hs) => pickBase k ih c after h2 y s hk e hs
  | Zero, xs, c, after, h1, h2, hsa, y, s, hk, Inr (Both g hlen) =>
    Void.exfalso (Nat.lessIrrefl k (Nat.ltCongLeft (List.length s) k k hk
      (Nat.leTrans (Succ (List.length s)) (List.length xs) k (List.subsequenceLength (Cons y s) xs g) hlen)))
  | Succ w, Nil, c, after, h1, h2, hsa, y, s, hk, Inl (Both e hs) => pickBase k ih c after h2 y s hk e hs
  | Succ w, Nil, c, after, h1, h2, hsa, y, s, hk, Inr (Both g hlen) => Void.exfalso g
  | Succ w, Cons x more, c, after, h1, h2, hsa, y, s, hk, cand =>
    rewrite pickStep w x more c after in
      pickBestStep k w x more c after
        (c2 a2 g1 g2 g3 y2 s2 g5 g6 => pickBest k ih w more c2 a2 g1 g2 g3 y2 s2 g5 g6)
        (Nat.addSuccLeSucc k w (List.length more) h1) h2 hsa y s hk cand

theorem bestOptimal: (k: Nat) -> BestBelow k
  | Zero,   bank,        Nil,      h, hk => rfl
  | Zero,   bank,        Cons y s, h, hk => Void.exfalso (Nat.succNotZero (List.length s) hk)
  | Succ k, Nil,         Nil,      h, hk => Void.exfalso (Nat.zeroNotSucc k hk)
  | Succ k, Nil,         Cons y s, h, hk => Void.exfalso h
  | Succ k, Cons d rest, Nil,      h, hk => Void.exfalso (Nat.zeroNotSucc k hk)
  | Succ k, Cons d rest, Cons y s, h, hk =>
    bestOptimalStep k d rest y s (l t g gk => bestOptimal k l t g gk) h (Nat.succInjective (List.length s) k hk)

theorem bestOptimalStep (k: Nat) (d: Fin 10) (rest: Bank) (y: Fin 10) (s: Bank) (ih: BestBelow k)
  (h: List.Subsequence (Cons y s) (Cons d rest)) (hk: List.length s = k):
  number (Cons y s) <= number (Bank.best (Succ k) (Cons d rest)) :=
  pickBest k ih (List.length rest - k) rest d rest
    (Nat.addSubLe k (List.length rest) (Nat.leCongLeft (List.length s) k (List.length rest) hk (List.subsequenceLength (Cons y s) (Cons d rest) h)))
    (Nat.leCongLeft (List.length s) k (List.length rest) hk (List.subsequenceLength (Cons y s) (Cons d rest) h))
    (t g => g) y s hk
    (Or.andWith (Nat.leSubAdd k (List.length rest) (Nat.leCongLeft (List.length s) k (List.length rest) hk (List.subsequenceLength (Cons y s) (Cons d rest) h))) h)

-- 4. For every bank: no k batteries, taken in order, make more joltage than
-- the greedy pick.
theorem bestIsLargest (k: Nat) (bank: Bank) (s: List (Fin 10)) (h: List.Subsequence s bank) (hk: List.length s = k):
  number s <= joltage k bank := bestOptimal k bank s h hk
