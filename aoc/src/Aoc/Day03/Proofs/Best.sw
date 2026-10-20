-- Day 3, proved: the greedy `Bank.best` is the largest k-digit number that can
-- be picked from a bank, in order, for any k and any digits. Kept apart from
-- the program, so `stitchwort run Aoc.Day03.main` doesn't check it.

namespace Aoc.Day03.Proofs
import Aoc.Day03 (..)
import Std (Eq)

-- Parsing gives digits, so this holds for every line of the input: no k
-- batteries beat the joltage computed.

theorem joltageIsLargest (k: Nat) (line: Text) (s: List Nat) (h: List.Subsequence s (Bank.parse line)) (hk: List.length s = k):
  Nat.fromDigits s <= joltage k (Bank.parse line) := bestIsLargest k (Bank.parse line) s (Char.mapDigitValueDigits (Text.toList line)) h hk

-- Three facts about `best k ds` (plain-words summary in docs/aoc-2025.md):
--   1. `bestSub`: it is a subsequence of `ds` (digits taken in order).
--   2. `bestLength`: it has `min k (length ds)` digits.
--   3. `bestOptimal` / `bestIsLargest`: no k digits of `ds`, taken in
--      order, make a larger number.
-- The optimality argument: every choice starts with some digit y inside the
-- window that `pick` scans (it must leave k - 1 digits after it). If y is
-- below pick's digit, the choice loses on its first digit
-- (`Nat.fromDigitsHeadLess`). If y equals it, y is at pick's position or
-- later, since pick takes the leftmost largest, so the rest of the choice
-- comes from what follows pick's digit, where `best` (by induction on k)
-- does at least as well.

-- What `pick` returns.
theorem pickGe: (w: Nat) -> (xs: List Nat) -> (c: Nat) -> (after: List Nat) -> c <= Pair.fst (Bank.best.pick w xs c after)
  | Zero,   xs,          c, after => Nat.leRefl c
  | Succ w, Nil,         c, after => Nat.leRefl c
  | Succ w, Cons x more, c, after =>
    match e: Nat.leq (Succ c) x with
      | True  => Nat.leTrans c x (Pair.fst (Bank.best.pick w more x more)) (Nat.lessLe c x e) (pickGe w more x more)
      | False => pickGe w more c after

theorem pickLen (k: Nat): (w: Nat) -> (xs: List Nat) -> (c: Nat) -> (after: List Nat) ->
    k + w <= List.length xs -> k <= List.length after -> k <= List.length (Pair.snd (Bank.best.pick w xs c after))
  | Zero,   xs,          c, after, h1, h2 => h2
  | Succ w, Nil,         c, after, h1, h2 => h2
  | Succ w, Cons x more, c, after, h1, h2 =>
    match e: Nat.leq (Succ c) x with
      | True  => pickLen k w more x more (Nat.addSuccLeSucc k w (List.length more) h1) (Nat.leOfAddLe k w (List.length more) (Nat.addSuccLeSucc k w (List.length more) h1))
      | False => pickLen k w more c after (Nat.addSuccLeSucc k w (List.length more) h1) h2

theorem pickSub (t: List Nat): (w: Nat) -> (xs: List Nat) -> (c: Nat) -> (after: List Nat) ->
    ((s: List Nat) -> List.Subsequence s xs -> List.Subsequence s t) ->
    ((s: List Nat) -> List.Subsequence s after -> List.Subsequence (Cons c s) t) ->
    (s: List Nat) -> List.Subsequence s (Pair.snd (Bank.best.pick w xs c after)) -> List.Subsequence (Cons (Pair.fst (Bank.best.pick w xs c after)) s) t
  | Zero,   xs,          c, after, hx, hc, s, h => hc s h
  | Succ w, Nil,         c, after, hx, hc, s, h => hc s h
  | Succ w, Cons x more, c, after, hx, hc, s, h =>
    match e: Nat.leq (Succ c) x with
      | True  => pickSub t w more x more (s2 g2 => hx s2 (List.subsequenceCons x s2 more g2)) (s2 g2 => hx (Cons x s2) (Inl (Both rfl g2))) s h
      | False => pickSub t w more c after (s2 g2 => hx s2 (List.subsequenceCons x s2 more g2)) hc s h

-- 1. `best k ds` is a subsequence of `ds`.
theorem bestSub: (k: Nat) -> (ds: List Nat) -> List.Subsequence (Bank.best k ds) ds
  | Zero,   ds          => Trivial
  | Succ k, Nil         => Trivial
  | Succ k, Cons d rest =>
    pickSub (Cons d rest) (List.length rest - k) rest d rest (s h => List.subsequenceCons d s rest h) (s h => Inl (Both rfl h))
      (Bank.best k (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest))) (bestSub k (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest)))

theorem bestLengthStep (k: Nat) (d: Nat) (rest: List Nat)
  (ih: (a: List Nat) -> List.length (Bank.best k a) = Nat.min k (List.length a)):
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

-- 2. `best k ds` has k digits, or all of them if there are fewer.
theorem bestLength: (k: Nat) -> (ds: List Nat) -> List.length (Bank.best k ds) = Nat.min k (List.length ds)
  | Zero,   ds          => rfl
  | Succ k, Nil         => rfl
  | Succ k, Cons d rest => bestLengthStep k d rest (a => bestLength k a)

-- 3. No k digits of `ds`, in order, make a larger number than `best k ds`.

-- What `best k` is claimed to do: beat every k digits taken from `l`.
def BestBelow (k: Nat): Prop :=
  (l: List Nat) -> (s: List Nat) -> List.Subsequence s l -> Nat.Digits s -> List.length s = k -> Nat.fromDigits s <= Nat.fromDigits (Bank.best k l)

-- The choices `pick` has seen so far: `y` followed by `s` is either the
-- current candidate `c` followed by digits from `after`, or a digit within
-- the next `w` of `xs` followed by digits from after it.
def Candidate (k: Nat) (w: Nat) (xs: List Nat) (c: Nat) (after: List Nat) (y: Nat) (s: List Nat): Prop :=
  Or (And (y = c) (List.Subsequence s after)) (And (List.Subsequence (Cons y s) xs) (List.length xs <= w + k))

-- `pick`'s choice, followed by `best k` of what comes after it, beats them all.
def PickBeats (k: Nat) (w: Nat) (xs: List Nat) (c: Nat) (after: List Nat): Prop :=
  k + w <= List.length xs -> k <= List.length after -> ((s: List Nat) -> List.Subsequence s xs -> List.Subsequence s after) ->
  (y: Nat) -> (s: List Nat) -> Nat.Digits s -> List.length s = k -> Candidate k w xs c after y s ->
  Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons (Pair.fst (Bank.best.pick w xs c after)) (Bank.best k (Pair.snd (Bank.best.pick w xs c after))))

-- `best k` of what follows the pick has k digits.
theorem pickRestLength (k: Nat) (w: Nat) (more: List Nat) (c: Nat) (after: List Nat) (h1: k + w <= List.length more) (h2: k <= List.length after):
  List.length (Bank.best k (Pair.snd (Bank.best.pick w more c after))) = k :=
  calc List.length (Bank.best k (Pair.snd (Bank.best.pick w more c after)))
    _ = Nat.min k (List.length (Pair.snd (Bank.best.pick w more c after))) := bestLength k (Pair.snd (Bank.best.pick w more c after))
    _ = k := Nat.minLeft k (List.length (Pair.snd (Bank.best.pick w more c after))) (pickLen k w more c after h1 h2)

-- A choice starting below pick's choice loses.
theorem pickBeatsSmaller (k: Nat) (w: Nat) (more: List Nat) (c: Nat) (after: List Nat) (h1: k + w <= List.length more) (h2: k <= List.length after)
  (y: Nat) (s: List Nat) (hd: Nat.Digits s) (hk: List.length s = k) (lt: y < Pair.fst (Bank.best.pick w more c after)):
  Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons (Pair.fst (Bank.best.pick w more c after)) (Bank.best k (Pair.snd (Bank.best.pick w more c after)))) :=
  Nat.fromDigitsHeadLess y (Pair.fst (Bank.best.pick w more c after)) s (Bank.best k (Pair.snd (Bank.best.pick w more c after))) (Eq.trans hk (Eq.sym (pickRestLength k w more c after h1 h2))) hd lt

-- With nothing left to scan, `pick` keeps `c`.
theorem pickBase (k: Nat) (ih: BestBelow k) (c: Nat) (after: List Nat) (h2: k <= List.length after)
  (y: Nat) (s: List Nat) (hd: Nat.Digits s) (hk: List.length s = k) (e: y = c) (hs: List.Subsequence s after):
  Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons c (Bank.best k after)) :=
  calc Nat.fromDigits (Cons y s)
    _ = Nat.fromDigits (Cons c s) := Eq.cong (z => Nat.fromDigits (Cons z s)) e
    _ <= Nat.fromDigits (Cons c (Bank.best k after)) := Nat.fromDigitsConsLe c s (Bank.best k after) (Eq.trans hk (Eq.sym (Eq.trans (bestLength k after) (Nat.minLeft k (List.length after) h2)))) (ih after s hs hd hk)

-- When `x` ties with `c`, starting from `x` is no better than from `c`, which
-- comes earlier.
theorem pickTie (k: Nat) (w: Nat) (x: Nat) (more: List Nat) (c: Nat) (after: List Nat)
  (rec: (c2: Nat) -> (a2: List Nat) -> PickBeats k w more c2 a2)
  (h1: k + w <= List.length more) (h2: k <= List.length after) (hsa: (s: List Nat) -> List.Subsequence s (Cons x more) -> List.Subsequence s after)
  (y: Nat) (s: List Nat) (hd: Nat.Digits s) (hk: List.length s = k) (le: x <= c) (eyx: y = x) (hs: List.Subsequence s more):
  Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons (Pair.fst (Bank.best.pick w more c after)) (Bank.best k (Pair.snd (Bank.best.pick w more c after)))) :=
  match e2: Nat.leq (Succ x) c with
    | True =>
      pickBeatsSmaller k w more c after h1 h2 y s hd hk
        (Nat.ltCongLeft x y (Pair.fst (Bank.best.pick w more c after)) (Eq.sym eyx) (Nat.leTrans (Succ x) c (Pair.fst (Bank.best.pick w more c after)) e2 (pickGe w more c after)))
    | False =>
      rec c after h1 h2 (t h => hsa t (List.subsequenceCons x t more h)) y s hd hk
        (Inl (Both (Eq.trans eyx (Nat.leAntisym x c le (Nat.leqFalse (Succ x) c e2))) (hsa s (List.subsequenceCons x s more hs))))

theorem pickBestStep (k: Nat) (w: Nat) (x: Nat) (more: List Nat) (c: Nat) (after: List Nat)
  (rec: (c2: Nat) -> (a2: List Nat) -> PickBeats k w more c2 a2)
  (h1: k + w <= List.length more) (h2: k <= List.length after) (hsa: (s: List Nat) -> List.Subsequence s (Cons x more) -> List.Subsequence s after)
  (y: Nat) (s: List Nat) (hd: Nat.Digits s) (hk: List.length s = k) (cand: Candidate k (Succ w) (Cons x more) c after y s):
    Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons (Pair.fst (Decidable.elim (Bool.decTrue (Nat.leq (Succ c) x)) (u => Bank.best.pick w more x more) (u => Bank.best.pick w more c after)))
      (Bank.best k (Pair.snd (Decidable.elim (Bool.decTrue (Nat.leq (Succ c) x)) (u => Bank.best.pick w more x more) (u => Bank.best.pick w more c after))))) :=
  match e: Nat.leq (Succ c) x, cand with
    | True, Inl (Both ey hs) =>
      pickBeatsSmaller k w more x more h1 (Nat.leOfAddLe k w (List.length more) h1) y s hd hk
        (Nat.ltCongLeft c y (Pair.fst (Bank.best.pick w more x more)) (Eq.sym ey) (Nat.leTrans (Succ c) x (Pair.fst (Bank.best.pick w more x more)) e (pickGe w more x more)))
    | True, Inr (Both g hlen) =>
      rec x more h1 (Nat.leOfAddLe k w (List.length more) h1) (t h => h) y s hd hk (Or.andWith hlen g)
    | False, Inl a => rec c after h1 h2 (t h => hsa t (List.subsequenceCons x t more h)) y s hd hk (Inl a)
    | False, Inr (Both (Inr g) hlen) => rec c after h1 h2 (t h => hsa t (List.subsequenceCons x t more h)) y s hd hk (Inr (Both g hlen))
    | False, Inr (Both (Inl (Both eyx hs)) hlen) =>
      pickTie k w x more c after rec h1 h2 hsa y s hd hk (Nat.leqFalse (Succ c) x e) eyx hs

theorem pickBest (k: Nat) (ih: BestBelow k): (w: Nat) -> (xs: List Nat) -> (c: Nat) -> (after: List Nat) -> PickBeats k w xs c after
  | Zero, xs, c, after, h1, h2, hsa, y, s, hd, hk, Inl (Both e hs) => pickBase k ih c after h2 y s hd hk e hs
  | Zero, xs, c, after, h1, h2, hsa, y, s, hd, hk, Inr (Both g hlen) =>
    Void.exfalso (Nat.lessIrrefl k (Nat.ltCongLeft (List.length s) k k hk
      (Nat.leTrans (Succ (List.length s)) (List.length xs) k (List.subsequenceLength (Cons y s) xs g) hlen)))
  | Succ w, Nil, c, after, h1, h2, hsa, y, s, hd, hk, Inl (Both e hs) => pickBase k ih c after h2 y s hd hk e hs
  | Succ w, Nil, c, after, h1, h2, hsa, y, s, hd, hk, Inr (Both g hlen) => Void.exfalso g
  | Succ w, Cons x more, c, after, h1, h2, hsa, y, s, hd, hk, cand =>
    pickBestStep k w x more c after
      (c2 a2 g1 g2 g3 y2 s2 g4 g5 g6 => pickBest k ih w more c2 a2 g1 g2 g3 y2 s2 g4 g5 g6)
      (Nat.addSuccLeSucc k w (List.length more) h1) h2 hsa y s hd hk cand

theorem bestOptimal: (k: Nat) -> BestBelow k
  | Zero,   ds,          Nil,      h, hd,        hk => rfl
  | Zero,   ds,          Cons y s, h, hd,        hk => Void.exfalso (Nat.succNotZero (List.length s) hk)
  | Succ k, Nil,         Nil,      h, hd,        hk => Void.exfalso (Nat.zeroNotSucc k hk)
  | Succ k, Nil,         Cons y s, h, hd,        hk => Void.exfalso h
  | Succ k, Cons d rest, Nil,      h, hd,        hk => Void.exfalso (Nat.zeroNotSucc k hk)
  | Succ k, Cons d rest, Cons y s, h, Both hy hs, hk =>
    bestOptimalStep k d rest y s (l t g gd gk => bestOptimal k l t g gd gk) h hs (Nat.succInjective (List.length s) k hk)

theorem bestOptimalStep (k: Nat) (d: Nat) (rest: List Nat) (y: Nat) (s: List Nat) (ih: BestBelow k)
  (h: List.Subsequence (Cons y s) (Cons d rest)) (hs: Nat.Digits s) (hk: List.length s = k):
  Nat.fromDigits (Cons y s) <= Nat.fromDigits (Bank.best (Succ k) (Cons d rest)) :=
  pickBest k ih (List.length rest - k) rest d rest
    (Nat.addSubLe k (List.length rest) (Nat.leCongLeft (List.length s) k (List.length rest) hk (List.subsequenceLength (Cons y s) (Cons d rest) h)))
    (Nat.leCongLeft (List.length s) k (List.length rest) hk (List.subsequenceLength (Cons y s) (Cons d rest) h))
    (t g => g) y s hs hk
    (Or.andWith (Nat.leSubAdd k (List.length rest) (Nat.leCongLeft (List.length s) k (List.length rest) hk (List.subsequenceLength (Cons y s) (Cons d rest) h))) h)

-- For a bank of digits: the greedy pick beats every choice of k digits.
theorem bestIsLargest (k: Nat) (ds: List Nat) (s: List Nat) (digits: Nat.Digits ds) (h: List.Subsequence s ds) (hk: List.length s = k):
  Nat.fromDigits s <= Nat.fromDigits (Bank.best k ds) := bestOptimal k ds s h (Nat.digitsOfSubsequence s ds h digits) hk
