-- Advent of Code 2025, day 3: each line is a bank of batteries with a digit
-- on each. Pick k batteries, in order, to make the largest k-digit number
-- (2 digits in part 1, 12 in part 2). Sum the best number over the banks.
--
--   $ stitchwort run aoc/day03.sw < aoc/inputs/day03.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- Greedy: the first digit is the largest one in the part of the bank that
-- still leaves k - 1 digits after it, taking the leftmost such digit so the
-- most is left over; then repeat on what follows it.

def main () : {IO} () :=
  let (one, two) := solve (IO.readAllLines ())
  print ("Part 1: " ++ one.toText)
  print ("Part 2: " ++ two.toText)

def solve (lines : List Text) : (Nat, Nat) := (total 2 lines, total 12 lines)

def total (k : Nat) (lines : List Text) : Nat := lines |> .sumBy (joltage k)

def joltage (k : Nat) (line : Text) : Nat :=
  line |> Bank.parse |> .best k |> Nat.fromDigits

-- A bank of batteries: one digit per battery.
def Bank : Type := List Nat

def Bank.parse (t : Text) : Bank := t.toList |> .mapMaybe Char.digitValue

-- The digits of the largest k-digit number that is a subsequence of ds.
def Bank.best : Nat -> Bank -> Bank
  | Zero,   _           => []
  | Succ _, []          => []
  | Succ k, Cons d rest =>
    -- The leftmost largest of the next w digits, and what follows it. The
    -- candidate so far is c, followed by `after`.
    def pick : Nat -> List Nat -> Nat -> List Nat -> (Nat, List Nat)
      | Zero,   _,           c, after => (c, after)
      | Succ _, [],          c, after => (c, after)
      | Succ w, Cons x more, c, after =>
        if c < x then pick w more x more else pick w more c after
    let chosen := pick (rest.length - k) rest d rest
    Cons chosen.fst (Bank.best k chosen.snd)

-- Examples -----------------------------------------------------------------

def example : List Text := ["987654321111111", "811111111111119", "234234234234278", "818181911112111"]

test "example" := solve example == (357, 3121910778619)
test "banks part 1" := example.map (joltage 2) == [98, 89, 78, 92]
test "banks part 2" := example.map (joltage 12) == [987654321111, 811111111119, 434234234278, 888911112111]
test "parse" := Bank.parse "102" == [1, 0, 2]
test "zeros" := Bank.best 2 [0, 0, 5, 0] == [5, 0]
test "leftmost wins" := Bank.best 1 [3, 9, 9, 1] == [9]
test "keep everything" := Bank.best 3 [4, 5, 6] == [4, 5, 6]
test "too short" := Bank.best 5 [1, 2] == [1, 2]

theorem exampleAnswer : solve example = (357, 3121910778619) := rfl

theorem bestNone : Bank.best 0 [1, 2, 3] = Nil := rfl

theorem bestAll : Bank.best 3 [4, 5, 6] = [4, 5, 6] := rfl

-- Proofs -------------------------------------------------------------------
--
-- Three facts about `best k ds` (plain-words summary in docs/aoc-2025.md):
--   1. `bestSub`: it is a subsequence of `ds` (digits taken in order).
--   2. `bestLength`: it has `min k (length ds)` digits.
--   3. `bestOptimal` / `joltageIsLargest`: no k digits of `ds`, taken in
--      order, make a larger number.
-- The optimality argument: every choice starts with some digit y inside the
-- window that `pick` scans (it must leave k - 1 digits after it). If y is
-- below pick's digit, the choice loses on its first digit (`headLess`). If
-- y equals it, y is at pick's position or later, since pick takes the
-- leftmost largest, so the rest of the choice comes from what follows
-- pick's digit, where `best` (by induction on k) does at least as well.

-- Every element is a decimal digit.
def Digits : List Nat -> Prop
  | Nil       => Unit
  | Cons d ds => And (d < 10) (Digits ds)

theorem subDigits : (s : List Nat) -> (ds : List Nat) -> List.Subsequence s ds -> Digits ds -> Digits s
  | Nil,       ds,        h,              hd          => Trivial
  | Cons x xs, Nil,       h,              hd          => Void.exfalso h
  | Cons x xs, Cons y ys, Inl (Both e h), Both hy hys => Both (Nat.ltCongLeft y x 10 (Eq.sym e) hy) (subDigits xs ys h hys)
  | Cons x xs, Cons y ys, Inr h,          Both hy hys => subDigits (Cons x xs) ys h hys

theorem orWith : [p q r : Prop] -> r -> Or p q -> Or p (And q r)
  | hr, Inl a => Inl a
  | hr, Inr b => Inr (Both b hr)

-- Arithmetic on digit lists.

-- `Nat.fromDigitsCons`, with the power written for another list of the
-- same length.
theorem fromDigitsConsLen (d : Nat) (s : List Nat) (r : List Nat) (hl : List.length s = List.length r) :
  Nat.fromDigits (Cons d s) = d * Nat.pow 10 (List.length r) + Nat.fromDigits s :=
  Eq.trans (Nat.fromDigitsCons d s) (Eq.cong (\n => d * Nat.pow 10 n + Nat.fromDigits s) hl)

-- `y * p + p` is at most `t * p` when `y < t`.
theorem nextMultipleLe (y : Nat) (t : Nat) (p : Nat) (h : y < t) : y * p + p <= t * p :=
  Nat.leCongLeft (Succ y * p) (y * p + p) (t * p) (Nat.addComm p (y * p)) (Nat.leMulRight (Succ y) t p h)

-- n digits make a number below 10^n.
theorem fromDigitsBound : (s : List Nat) -> Digits s -> Nat.fromDigits s < Nat.pow 10 (List.length s)
  | Nil,      h          => rfl
  | Cons d s, Both hd hs =>
    Nat.ltCongLeft (d * Nat.pow 10 (List.length s) + Nat.fromDigits s) (Nat.fromDigits (Cons d s)) (10 * Nat.pow 10 (List.length s))
      (Eq.sym (Nat.fromDigitsCons d s))
      (Nat.leTrans (Succ (d * Nat.pow 10 (List.length s) + Nat.fromDigits s)) (d * Nat.pow 10 (List.length s) + Nat.pow 10 (List.length s)) (10 * Nat.pow 10 (List.length s))
        (Nat.ltAddCong (d * Nat.pow 10 (List.length s)) (Nat.fromDigits s) (Nat.pow 10 (List.length s)) (fromDigitsBound s hs))
        (nextMultipleLe d 10 (Nat.pow 10 (List.length s)) hd))

theorem headLessArith (y : Nat) (t : Nat) (p : Nat) (vs : Nat) (vr : Nat) (bound : vs < p) (h : y < t) : y * p + vs <= t * p + vr :=
  Nat.leTrans (y * p + vs) (t * p) (t * p + vr)
    (Nat.leTrans (y * p + vs) (y * p + p) (t * p) (Nat.lessLe (y * p + vs) (y * p + p) (Nat.ltAddCong (y * p) vs p bound)) (nextMultipleLe y t p h))
    (Nat.leAddRight (t * p) vr)

-- Equal-length numbers: a smaller first digit gives a smaller number.
theorem headLess (y : Nat) (t : Nat) (s : List Nat) (r : List Nat) (hl : List.length s = List.length r)
  (hd : Digits s) (h : y < t) : Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons t r) :=
  Nat.leCongLeft (y * Nat.pow 10 (List.length r) + Nat.fromDigits s) (Nat.fromDigits (Cons y s)) (Nat.fromDigits (Cons t r))
    (Eq.sym (fromDigitsConsLen y s r hl))
    (Nat.leCongRight (y * Nat.pow 10 (List.length r) + Nat.fromDigits s) (t * Nat.pow 10 (List.length r) + Nat.fromDigits r) (Nat.fromDigits (Cons t r))
      (Eq.sym (Nat.fromDigitsCons t r))
      (headLessArith y t (Nat.pow 10 (List.length r)) (Nat.fromDigits s) (Nat.fromDigits r)
        (Nat.ltCongRight (Nat.fromDigits s) (Nat.pow 10 (List.length s)) (Nat.pow 10 (List.length r)) (Eq.cong (\n => Nat.pow 10 n) hl) (fromDigitsBound s hd))
        h))

-- Equal-length numbers with the same first digit: the rest decides.
theorem consLe (c : Nat) (s : List Nat) (r : List Nat) (hl : List.length s = List.length r)
  (h : Nat.fromDigits s <= Nat.fromDigits r) : Nat.fromDigits (Cons c s) <= Nat.fromDigits (Cons c r) :=
  Nat.leCongLeft (c * Nat.pow 10 (List.length r) + Nat.fromDigits s) (Nat.fromDigits (Cons c s)) (Nat.fromDigits (Cons c r))
    (Eq.sym (fromDigitsConsLen c s r hl))
    (Nat.leCongRight (c * Nat.pow 10 (List.length r) + Nat.fromDigits s) (c * Nat.pow 10 (List.length r) + Nat.fromDigits r) (Nat.fromDigits (Cons c r))
      (Eq.sym (Nat.fromDigitsCons c r))
      (Nat.leAddCong (c * Nat.pow 10 (List.length r)) (Nat.fromDigits s) (Nat.fromDigits r) h))

-- k digits fit in a bank of n when k <= n: the window of `n - k` leaves
-- exactly k after it.
theorem windowFits (k : Nat) (n : Nat) (room : k <= n) : k + (n - k) <= n :=
  Nat.leCongRight (k + (n - k)) (k + (n - k)) n (Nat.addSubCancel k n room) (Nat.leRefl (k + (n - k)))

theorem windowCovers (k : Nat) (n : Nat) (room : k <= n) : n <= (n - k) + k :=
  Nat.leCongRight n n ((n - k) + k) (Eq.trans (Eq.sym (Nat.addSubCancel k n room)) (Nat.addComm k (n - k))) (Nat.leRefl n)

theorem windowStep (k : Nat) (w : Nat) (n : Nat) (h : k + Succ w <= Succ n) : k + w <= n :=
  Nat.leCongLeft (k + Succ w) (Succ (k + w)) (Succ n) (Nat.addSucc k w) h

theorem windowRoom (k : Nat) (w : Nat) (n : Nat) (h : k + w <= n) : k <= n := Nat.leTrans k (k + w) n (Nat.leAddRight k w) h

-- What `pick` returns.

theorem pickGe : (w : Nat) -> (xs : List Nat) -> (c : Nat) -> (after : List Nat) -> c <= Pair.fst (Bank.best.pick w xs c after)
  | Zero,   xs,          c, after => Nat.leRefl c
  | Succ w, Nil,         c, after => Nat.leRefl c
  | Succ w, Cons x more, c, after =>
    Bool.inspect (Nat.leq (Succ c) x)
      (\b => c <= Pair.fst (Decidable.elim (Bool.decTrue b) (\u => Bank.best.pick w more x more) (\u => Bank.best.pick w more c after)))
      (\e => Nat.leTrans c x (Pair.fst (Bank.best.pick w more x more)) (Nat.lessLe c x e) (pickGe w more x more))
      (\e => pickGe w more c after)

theorem pickLen (k : Nat) : (w : Nat) -> (xs : List Nat) -> (c : Nat) -> (after : List Nat) ->
    k + w <= List.length xs -> k <= List.length after -> k <= List.length (Pair.snd (Bank.best.pick w xs c after))
  | Zero,   xs,          c, after, h1, h2 => h2
  | Succ w, Nil,         c, after, h1, h2 => h2
  | Succ w, Cons x more, c, after, h1, h2 =>
    Bool.inspect (Nat.leq (Succ c) x)
      (\b => k <= List.length (Pair.snd (Decidable.elim (Bool.decTrue b) (\u => Bank.best.pick w more x more) (\u => Bank.best.pick w more c after))))
      (\e => pickLen k w more x more (windowStep k w (List.length more) h1) (windowRoom k w (List.length more) (windowStep k w (List.length more) h1)))
      (\e => pickLen k w more c after (windowStep k w (List.length more) h1) h2)

theorem pickSub (t : List Nat) : (w : Nat) -> (xs : List Nat) -> (c : Nat) -> (after : List Nat) ->
    ((s : List Nat) -> List.Subsequence s xs -> List.Subsequence s t) ->
    ((s : List Nat) -> List.Subsequence s after -> List.Subsequence (Cons c s) t) ->
    (s : List Nat) -> List.Subsequence s (Pair.snd (Bank.best.pick w xs c after)) -> List.Subsequence (Cons (Pair.fst (Bank.best.pick w xs c after)) s) t
  | Zero,   xs,          c, after, hx, hc, s, h => hc s h
  | Succ w, Nil,         c, after, hx, hc, s, h => hc s h
  | Succ w, Cons x more, c, after, hx, hc, s, h =>
    Bool.inspect (Nat.leq (Succ c) x)
      (\b => List.Subsequence s (Pair.snd (Decidable.elim (Bool.decTrue b) (\u => Bank.best.pick w more x more) (\u => Bank.best.pick w more c after)))
        -> List.Subsequence (Cons (Pair.fst (Decidable.elim (Bool.decTrue b) (\u => Bank.best.pick w more x more) (\u => Bank.best.pick w more c after))) s) t)
      (\e g => pickSub t w more x more (\s2 g2 => hx s2 (List.subsequenceCons x s2 more g2)) (\s2 g2 => hx (Cons x s2) (Inl (Both rfl g2))) s g)
      (\e g => pickSub t w more c after (\s2 g2 => hx s2 (List.subsequenceCons x s2 more g2)) hc s g)
      h

-- 1. `best k ds` is a subsequence of `ds`.
theorem bestSub : (k : Nat) -> (ds : List Nat) -> List.Subsequence (Bank.best k ds) ds
  | Zero,   ds          => Trivial
  | Succ k, Nil         => Trivial
  | Succ k, Cons d rest =>
    pickSub (Cons d rest) (List.length rest - k) rest d rest (\s h => List.subsequenceCons d s rest h) (\s h => Inl (Both rfl h))
      (Bank.best k (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest))) (bestSub k (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest)))

theorem bestLengthStep (k : Nat) (d : Nat) (rest : List Nat)
  (ih : (a : List Nat) -> List.length (Bank.best k a) = Nat.min k (List.length a)) : (b : Bool) -> Nat.leq k (List.length rest) = b ->
    Succ (List.length (Bank.best k (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest)))) = Bool.ifThenElse b (\u => Succ k) (\u => Succ (List.length rest))
  | True, e =>
    Eq.cong Succ (Eq.trans (ih (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest)))
      (Nat.minLeft k (List.length (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest)))
        (pickLen k (List.length rest - k) rest d rest (windowFits k (List.length rest) e) e)))
  | False, e =>
    Eq.cong Succ (Eq.trans (ih (Pair.snd (Bank.best.pick (List.length rest - k) rest d rest)))
      (Eq.trans (Eq.cong (\w => Nat.min k (List.length (Pair.snd (Bank.best.pick w rest d rest))))
          (Nat.subEqZero (List.length rest) k (Nat.lessLe (List.length rest) k (Nat.leqFalse k (List.length rest) e))))
        (Nat.minRight k (List.length rest) e)))

-- 2. `best k ds` has k digits, or all of them if there are fewer.
theorem bestLength : (k : Nat) -> (ds : List Nat) -> List.length (Bank.best k ds) = Nat.min k (List.length ds)
  | Zero,   ds          => rfl
  | Succ k, Nil         => rfl
  | Succ k, Cons d rest => bestLengthStep k d rest (\a => bestLength k a) (Nat.leq k (List.length rest)) rfl

-- 3. No k digits of `ds`, in order, make a larger number than `best k ds`.

-- What `best k` is claimed to do: beat every k digits taken from `l`.
def BestBelow (k : Nat) : Prop :=
  (l : List Nat) -> (s : List Nat) -> List.Subsequence s l -> Digits s -> List.length s = k -> Nat.fromDigits s <= Nat.fromDigits (Bank.best k l)

-- The choices `pick` has seen so far: `y` followed by `s` is either the
-- current candidate `c` followed by digits from `after`, or a digit within
-- the next `w` of `xs` followed by digits from after it.
def Candidate (k : Nat) (w : Nat) (xs : List Nat) (c : Nat) (after : List Nat) (y : Nat) (s : List Nat) : Prop :=
  Or (And (y = c) (List.Subsequence s after)) (And (List.Subsequence (Cons y s) xs) (List.length xs <= w + k))

-- `pick`'s choice, followed by `best k` of what comes after it, beats them all.
def PickBeats (k : Nat) (w : Nat) (xs : List Nat) (c : Nat) (after : List Nat) : Prop :=
  k + w <= List.length xs -> k <= List.length after -> ((s : List Nat) -> List.Subsequence s xs -> List.Subsequence s after) ->
  (y : Nat) -> (s : List Nat) -> Digits s -> List.length s = k -> Candidate k w xs c after y s ->
  Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons (Pair.fst (Bank.best.pick w xs c after)) (Bank.best k (Pair.snd (Bank.best.pick w xs c after))))

-- `best k` of what follows the pick has k digits.
theorem pickRestLength (k : Nat) (w : Nat) (more : List Nat) (c : Nat) (after : List Nat) (h1 : k + w <= List.length more) (h2 : k <= List.length after) :
  List.length (Bank.best k (Pair.snd (Bank.best.pick w more c after))) = k :=
  Eq.trans (bestLength k (Pair.snd (Bank.best.pick w more c after))) (Nat.minLeft k (List.length (Pair.snd (Bank.best.pick w more c after))) (pickLen k w more c after h1 h2))

-- A choice starting below pick's choice loses.
theorem pickBeatsSmaller (k : Nat) (w : Nat) (more : List Nat) (c : Nat) (after : List Nat) (h1 : k + w <= List.length more) (h2 : k <= List.length after)
  (y : Nat) (s : List Nat) (hd : Digits s) (hk : List.length s = k) (lt : y < Pair.fst (Bank.best.pick w more c after)) :
  Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons (Pair.fst (Bank.best.pick w more c after)) (Bank.best k (Pair.snd (Bank.best.pick w more c after)))) :=
  headLess y (Pair.fst (Bank.best.pick w more c after)) s (Bank.best k (Pair.snd (Bank.best.pick w more c after))) (Eq.trans hk (Eq.sym (pickRestLength k w more c after h1 h2))) hd lt

-- With nothing left to scan, `pick` keeps `c`.
theorem pickBase (k : Nat) (ih : BestBelow k) (c : Nat) (after : List Nat) (h2 : k <= List.length after)
  (y : Nat) (s : List Nat) (hd : Digits s) (hk : List.length s = k) (e : y = c) (hs : List.Subsequence s after) :
  Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons c (Bank.best k after)) :=
  J (\z q => Nat.fromDigits (Cons z s) <= Nat.fromDigits (Cons c (Bank.best k after)))
    (consLe c s (Bank.best k after) (Eq.trans hk (Eq.sym (Eq.trans (bestLength k after) (Nat.minLeft k (List.length after) h2)))) (ih after s hs hd hk))
    (Eq.sym e)

-- When `x` ties with `c`, starting from `x` is no better than from `c`, which
-- comes earlier.
theorem pickTie (k : Nat) (w : Nat) (x : Nat) (more : List Nat) (c : Nat) (after : List Nat)
  (rec : (c2 : Nat) -> (a2 : List Nat) -> PickBeats k w more c2 a2)
  (h1 : k + w <= List.length more) (h2 : k <= List.length after) (hsa : (s : List Nat) -> List.Subsequence s (Cons x more) -> List.Subsequence s after)
  (y : Nat) (s : List Nat) (hd : Digits s) (hk : List.length s = k) (le : x <= c) (eyx : y = x) (hs : List.Subsequence s more) :
  (b : Bool) -> Nat.leq (Succ x) c = b ->
  Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons (Pair.fst (Bank.best.pick w more c after)) (Bank.best k (Pair.snd (Bank.best.pick w more c after))))
  | True, e2 =>
    pickBeatsSmaller k w more c after h1 h2 y s hd hk
      (Nat.ltCongLeft x y (Pair.fst (Bank.best.pick w more c after)) (Eq.sym eyx) (Nat.leTrans (Succ x) c (Pair.fst (Bank.best.pick w more c after)) e2 (pickGe w more c after)))
  | False, e2 =>
    rec c after h1 h2 (\t h => hsa t (List.subsequenceCons x t more h)) y s hd hk
      (Inl (Both (Eq.trans eyx (Nat.leAntisym x c le (Nat.leqFalse (Succ x) c e2))) (hsa s (List.subsequenceCons x s more hs))))

theorem pickBestStep (k : Nat) (w : Nat) (x : Nat) (more : List Nat) (c : Nat) (after : List Nat)
  (rec : (c2 : Nat) -> (a2 : List Nat) -> PickBeats k w more c2 a2)
  (h1 : k + w <= List.length more) (h2 : k <= List.length after) (hsa : (s : List Nat) -> List.Subsequence s (Cons x more) -> List.Subsequence s after)
  (y : Nat) (s : List Nat) (hd : Digits s) (hk : List.length s = k) : (b : Bool) -> Nat.leq (Succ c) x = b ->
    Candidate k (Succ w) (Cons x more) c after y s ->
    Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons (Pair.fst (Decidable.elim (Bool.decTrue b) (\u => Bank.best.pick w more x more) (\u => Bank.best.pick w more c after)))
      (Bank.best k (Pair.snd (Decidable.elim (Bool.decTrue b) (\u => Bank.best.pick w more x more) (\u => Bank.best.pick w more c after)))))
  | True, e, Inl (Both ey hs) =>
    pickBeatsSmaller k w more x more h1 (windowRoom k w (List.length more) h1) y s hd hk
      (Nat.ltCongLeft c y (Pair.fst (Bank.best.pick w more x more)) (Eq.sym ey) (Nat.leTrans (Succ c) x (Pair.fst (Bank.best.pick w more x more)) e (pickGe w more x more)))
  | True, e, Inr (Both g hlen) =>
    rec x more h1 (windowRoom k w (List.length more) h1) (\t h => h) y s hd hk (orWith hlen g)
  | False, e, Inl a => rec c after h1 h2 (\t h => hsa t (List.subsequenceCons x t more h)) y s hd hk (Inl a)
  | False, e, Inr (Both (Inr g) hlen) => rec c after h1 h2 (\t h => hsa t (List.subsequenceCons x t more h)) y s hd hk (Inr (Both g hlen))
  | False, e, Inr (Both (Inl (Both eyx hs)) hlen) =>
    pickTie k w x more c after rec h1 h2 hsa y s hd hk (Nat.leqFalse (Succ c) x e) eyx hs (Nat.leq (Succ x) c) rfl

theorem pickBest (k : Nat) (ih : BestBelow k) : (w : Nat) -> (xs : List Nat) -> (c : Nat) -> (after : List Nat) -> PickBeats k w xs c after
  | Zero, xs, c, after, h1, h2, hsa, y, s, hd, hk, Inl (Both e hs) => pickBase k ih c after h2 y s hd hk e hs
  | Zero, xs, c, after, h1, h2, hsa, y, s, hd, hk, Inr (Both g hlen) =>
    Void.exfalso (Nat.lessIrrefl k (Nat.ltCongLeft (List.length s) k k hk
      (Nat.leTrans (Succ (List.length s)) (List.length xs) k (List.subsequenceLength (Cons y s) xs g) hlen)))
  | Succ w, Nil, c, after, h1, h2, hsa, y, s, hd, hk, Inl (Both e hs) => pickBase k ih c after h2 y s hd hk e hs
  | Succ w, Nil, c, after, h1, h2, hsa, y, s, hd, hk, Inr (Both g hlen) => Void.exfalso g
  | Succ w, Cons x more, c, after, h1, h2, hsa, y, s, hd, hk, cand =>
    pickBestStep k w x more c after
      (\c2 a2 g1 g2 g3 y2 s2 g4 g5 g6 => pickBest k ih w more c2 a2 g1 g2 g3 y2 s2 g4 g5 g6)
      (windowStep k w (List.length more) h1) h2 hsa y s hd hk (Nat.leq (Succ c) x) rfl cand

theorem bestOptimal : (k : Nat) -> BestBelow k
  | Zero,   ds,          Nil,      h, hd,        hk => rfl
  | Zero,   ds,          Cons y s, h, hd,        hk => Void.exfalso (Nat.succNotZero (List.length s) hk)
  | Succ k, Nil,         Nil,      h, hd,        hk => Void.exfalso (Nat.zeroNotSucc k hk)
  | Succ k, Nil,         Cons y s, h, hd,        hk => Void.exfalso h
  | Succ k, Cons d rest, Nil,      h, hd,        hk => Void.exfalso (Nat.zeroNotSucc k hk)
  | Succ k, Cons d rest, Cons y s, h, Both hy hs, hk =>
    bestOptimalStep k d rest y s (\l t g gd gk => bestOptimal k l t g gd gk) h hs (Nat.succInjective (List.length s) k hk)

theorem bestOptimalStep (k : Nat) (d : Nat) (rest : List Nat) (y : Nat) (s : List Nat) (ih : BestBelow k)
  (h : List.Subsequence (Cons y s) (Cons d rest)) (hs : Digits s) (hk : List.length s = k) :
  Nat.fromDigits (Cons y s) <= Nat.fromDigits (Bank.best (Succ k) (Cons d rest)) :=
  pickBest k ih (List.length rest - k) rest d rest
    (windowFits k (List.length rest) (Nat.leCongLeft (List.length s) k (List.length rest) hk (List.subsequenceLength (Cons y s) (Cons d rest) h)))
    (Nat.leCongLeft (List.length s) k (List.length rest) hk (List.subsequenceLength (Cons y s) (Cons d rest) h))
    (\t g => g) y s hs hk
    (orWith (windowCovers k (List.length rest) (Nat.leCongLeft (List.length s) k (List.length rest) hk (List.subsequenceLength (Cons y s) (Cons d rest) h))) h)

-- For a bank of digits: the greedy pick beats every choice of k digits.
theorem bestIsLargest (k : Nat) (ds : List Nat) (s : List Nat) (digits : Digits ds) (h : List.Subsequence s ds) (hk : List.length s = k) :
  Nat.fromDigits s <= Nat.fromDigits (Bank.best k ds) := bestOptimal k ds s h (subDigits s ds h digits) hk

-- Parsing gives digits, so this holds for every line of the input: no k
-- batteries beat the joltage computed.

def DigitOrNothing : Maybe Nat -> Prop
  | Nothing => Unit
  | Just n  => n < 10

theorem digitValueDigit (c : Char) : DigitOrNothing (Char.digitValue c) :=
  Bool.inspect (Nat.leq 48 (Char.toNat c))
    (\b => DigitOrNothing (Bool.ifThenElse b (\u => Bool.ifThenElse (Nat.leq (Char.toNat c) 57) (\u => Just (Char.toNat c - 48)) (\u => Nothing)) (\u => Nothing)))
    (\e1 => Bool.inspect (Nat.leq (Char.toNat c) 57)
      (\b => DigitOrNothing (Bool.ifThenElse b (\u => Just (Char.toNat c - 48)) (\u => Nothing)))
      (\e2 => Nat.subLtAdd (Char.toNat c) 48 10 e1 e2)
      (\e2 => Trivial))
    (\e1 => Trivial)

theorem consJustDigits : (m : Maybe Nat) -> (ys : List Nat) -> DigitOrNothing m -> Digits ys -> Digits (List.consJust m ys)
  | Nothing, ys, h, hy => hy
  | Just n,  ys, h, hy => Both h hy

theorem parseDigits : (cs : List Char) -> Digits (List.mapMaybe Char.digitValue cs)
  | Nil       => Trivial
  | Cons c cs => consJustDigits (Char.digitValue c) (List.mapMaybe Char.digitValue cs) (digitValueDigit c) (parseDigits cs)

theorem joltageIsLargest (k : Nat) (line : Text) (s : List Nat) (h : List.Subsequence s (Bank.parse line)) (hk : List.length s = k) :
  Nat.fromDigits s <= joltage k line := bestIsLargest k (Bank.parse line) s (parseDigits (Text.toList line)) h hk
