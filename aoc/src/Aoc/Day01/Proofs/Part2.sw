-- Day 1, part 2 proved correct: the arithmetic count of the clicks that land on
-- 0 agrees with turning the dial one click at a time, for a dial of any size.
-- Kept apart from the program, so `stitchwort run Aoc.Day01.main` doesn't
-- check it.
--
-- The lemmas about the dial are for a dial of any size, `Mod n`; with the
-- literal 100, `x % 100` unfolds to `x - 100 * (x / 100)` and `100 * q` to a
-- hundred additions, so every comparison of such types took seconds.

namespace Aoc.Day01.Proofs
import Aoc.Day01 (..)
import Aoc.Day01.Tests (example)
import Std (Bool, Eq, Int, List, Mod, Nat)

-- The specification of part 2: turn the dial one click at a time, and count
-- the positions after each click that are 0.
def zerosPassedSpec (start: Mod n) (turns: List Turn): Nat :=
  turns |> .concatMap Turn.clicks |> zerosLandedOn start

test "example, click by click" := zerosPassedSpec dial (parseTurns example) == 6

-- The zeros after each turn from `d`, counted by `List.occurrences`, which
-- suits proofs (it recurses on the list).
def zerosAfter (d: Mod n) (turns: List Turn): Nat :=
  List.occurrences isZero (List.drop 1 (List.scanLeft move d turns))

-- The clicks of one turn, then the rest.
theorem zerosPassedSplit [n: Nat] (d: Mod n) (t: Turn) (ts: List Turn):
    zerosAfter d (t.clicks ++ List.concatMap Turn.clicks ts)
      = zerosDuring d t + zerosAfter (move d t) (List.concatMap Turn.clicks ts) :=
  calc zerosAfter d (t.clicks ++ List.concatMap Turn.clicks ts)
    _ = zerosAfter d t.clicks + zerosAfter (List.foldLeft move d t.clicks) (List.concatMap Turn.clicks ts)
        := Eq.trans (Eq.cong (List.occurrences isZero) (List.scanLeftAppend move d t.clicks (List.concatMap Turn.clicks ts)))
             (List.occurrencesAppend isZero _ _)
    _ = zerosDuring d t + zerosAfter (List.foldLeft move d t.clicks) (List.concatMap Turn.clicks ts) := rewrite turnCount d t
    _ = zerosDuring d t + zerosAfter (move d t) (List.concatMap Turn.clicks ts)                      := rewrite turnAt d t

theorem zerosPassedFrom [n: Nat] (d: Mod n): (ts: List Turn) ->
    zerosPassed d ts = zerosAfter d (List.concatMap Turn.clicks ts)
  | Nil       => rfl
  | Cons t ts =>
    calc zerosPassed d (Cons t ts)
      _ = zerosDuring d t + zerosPassed (move d t) ts
          := List.sumCons (zerosDuring d t) (List.zipWith zerosDuring (List.scanLeft move (move d t) ts) ts)
      _ = zerosDuring d t + zerosAfter (move d t) (List.concatMap Turn.clicks ts) := rewrite zerosPassedFrom (move d t) ts
      _ = zerosAfter d (List.concatMap Turn.clicks (Cons t ts))                   := Eq.sym (zerosPassedSplit d t ts)

-- Positions stay on the dial by the type `Mod n`, and part 1's code reads as
-- the puzzle's own statement, so neither needs a theorem. The theorem,
-- `zerosPassedCorrect`, says the arithmetic count `zerosDuring` agrees with
-- turning the dial one click at a time, for any dial, start and turns. The
-- lemmas it rests on follow the definitions they are about.

-- The arithmetic count is the click-by-click count, for any dial,
-- start and turns.
theorem zerosPassedCorrect [n: Nat] (start: Mod n) (turns: List Turn): zerosPassed start turns = zerosPassedSpec start turns :=
  Eq.trans (zerosPassedFrom start turns)
    (Eq.sym (List.countOccurrences isZero (List.drop 1 (List.scanLeft move start (List.concatMap Turn.clicks turns)))))

-- And so for the puzzle's answer.
theorem part2Puzzle (turns: List Turn): solvePart2 turns = zerosPassedSpec dial turns :=
  zerosPassedCorrect dial turns

-- The lemmas below are about a dial with `Succ highest` positions, which is
-- what `Mod.size n` is (with `highest` as `n - 1`).

-- Where an integer lands on a dial numbered 0 to `highest`. Proofs only: it
-- keeps `Int.modNat` folded, which the checker would otherwise unfold in the
-- lemmas below.
def place (highest: Nat) (x: Int): Nat := Int.modNat x (Succ highest)

-- One click right on a dial of size `n`: from `a + 1 = n` the dial goes to
-- 0, otherwise to `a + 1`.
theorem rightCases (n: Nat) [auto ok: n != 0] (a: Nat) (h: a < n) (goal: Prop)
    (wraps: a + 1 = n -> goal) (below: Succ a < n -> goal): goal :=
  match e: Nat.leq n (Succ a) with
    | True  => wraps (Eq.trans (Nat.addOne a) (Nat.leAntisym (Succ a) n h e))
    | False => below (Nat.leqFalse n (Succ a) e)

theorem stepRightAt (d: Nat) [auto ok: d != 0] (a: Nat) (n: Nat):
    ((a + 1) % d + n) % d = (a + Succ n) % d :=
  calc ((a + 1) % d + n) % d
    _ = (a + 1 + n) % d  := Nat.modAddMod (a + 1) n d
    _ = (a + Succ n) % d := rewrite Nat.addAssoc a 1 n

theorem rightAt [n: Nat] (d: Mod n): (k: Nat) ->
    (List.foldLeft move d (List.replicate k (Right 1))).value = (d.value + k) % Mod.size n
  | Zero   => rewrite Nat.addZero d.value, Nat.modSmall d.value (Mod.size n) d.isLt
  | Succ k =>
    rewrite rightAt (move d (Right 1)) k, Mod.valueOfInt (d.toInt + Nat.toInt 1) in stepRightAt (Mod.size n) d.value k

-- One click left: from 0 to `highest`, otherwise down by one.
theorem leftZero (highest: Nat): place highest (Int.subNatNat 0 1) = highest := Int.modNatNegOne highest

theorem leftOne (highest: Nat) (m: Nat) (h: Succ m <= highest): place highest (Int.subNatNat (Succ m) 1) = m :=
  calc place highest (Int.subNatNat (Succ m) 1)
    _ = place highest (OfNat m) := Eq.cong (x => place highest x) (Eq.trans (Int.subNatNatSucc m 0) (Int.subNatNatZeroRight m))
    _ = m := Nat.modSmall m (Succ highest) (Nat.leTrans m (Succ m) highest (Nat.leSucc m) h)

theorem stepLeftAt (highest: Nat): (a: Nat) -> a <= highest -> (n: Nat) ->
    place highest (Nat.toInt (place highest (Int.subNatNat a 1)) - Nat.toInt n)
      = place highest (Int.subNatNat a (Succ n))
  | Zero,   h, n =>
    calc place highest (Nat.toInt (place highest (Int.subNatNat 0 1)) - Nat.toInt n)
      _ = place highest (Nat.toInt highest - Nat.toInt n)  := rewrite leftZero highest
      _ = place highest (Int.subNatNat highest n)          := rewrite Int.subOfNats highest n
      _ = place highest (Int.subNatNat 0 (Succ n) + Nat.toInt (Succ highest))
          := rewrite <- Eq.trans (Int.subNatNatAddOfNat (Succ highest) 0 (Succ n)) (Int.subNatNatSucc highest n)
      _ = place highest (Int.subNatNat 0 (Succ n))         := Int.modNatAddSize (Int.subNatNat 0 (Succ n)) (Succ highest)
  | Succ m, h, n =>
    rewrite leftOne highest m h, Int.subOfNats m n, Int.subNatNatSucc m n

theorem leftAt [n: Nat] (d: Mod n): (k: Nat) ->
    (List.foldLeft move d (List.replicate k (Left 1))).value = place (n - 1) (Nat.toInt d.value - Nat.toInt k)
  | Zero   => rewrite Nat.addZero d.value, Nat.modSmall d.value (Mod.size n) d.isLt
  | Succ k =>
    rewrite leftAt (move d (Left 1)) k, Mod.valueOfInt (d.toInt - Nat.toInt 1) in stepLeftAt (n - 1) d.value d.isLt k

theorem stepRight (d: Nat) [auto ok: d != 0] (a: Nat) (h: a < d) (n: Nat):
    Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d = (a + Succ n) / d :=
  rightCases d a h (Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d = (a + Succ n) / d)
    (e =>
      calc Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d
        _ = Succ (n / d)       := rewrite e, Nat.modSelf d
        _ = (d + n) / d        := Eq.sym (Nat.addDivSelf d n)
        _ = (Succ a + n) / d   := Eq.cong (x => (x + n) / d) (Eq.sym (Eq.trans (Eq.sym (Nat.addOne a)) e))
        _ = (a + Succ n) / d   := rewrite Nat.addSucc a n)
    (lt => rewrite Nat.addOne a, Nat.modSmall (Succ a) d lt, Nat.addSucc a n)

theorem rightCount [n: Nat] (d: Mod n): (k: Nat) ->
    zerosAfter d (List.replicate k (Right 1)) = (d.value + k) / Mod.size n
  | Zero   => rewrite Nat.addZero d.value, Nat.divSmall d.value (Mod.size n) d.isLt
  | Succ k =>
    calc zerosAfter d (List.replicate (Succ k) (Right 1))
      _ = Bool.toNat ((d.value + 1) % Mod.size n == 0) + ((d.value + 1) % Mod.size n + k) / Mod.size n
          := rewrite List.scanLeftCons move (move d (Right 1)) (List.replicate k (Right 1)), rightCount (move d (Right 1)) k, Mod.valueOfInt (d.toInt + Nat.toInt 1)
      _ = (d.value + Succ k) / Mod.size n := stepRight (Mod.size n) d.value d.isLt k

-- The count after one click left to `m`, from `Succ m`.
theorem stepLeftFrom (highest: Nat): (m: Nat) -> Succ m <= highest -> (n: Nat) ->
    Bool.toNat (m == 0) + ((Succ highest - m) % Succ highest + n) / Succ highest
      = ((Succ highest - Succ m) % Succ highest + Succ n) / Succ highest
  | Zero,   h, n =>
    rewrite Nat.modSelf (Succ highest), Nat.modSmall highest (Succ highest) (Nat.leRefl highest), Nat.addSucc highest n
      in Eq.sym (Nat.addDivSelf (Succ highest) n)
  | Succ j, h, n =>
    rewrite Nat.modSmall (highest - j) (Succ highest) (Nat.subLe highest j),
        Nat.modSmall (highest - Succ j) (Succ highest) (Nat.subLe highest (Succ j)),
        Nat.subSuccRight j highest (Nat.leTrans (Succ j) (Succ (Succ j)) highest (Nat.leSucc (Succ j)) h),
        Nat.addSucc (highest - Succ j) n
      in rfl

-- The count after one click left from 0, to `highest`.
theorem stepLeftTop: (highest: Nat) -> (n: Nat) ->
    Bool.toNat (highest == 0) + ((Succ highest - highest) % Succ highest + n) / Succ highest
      = ((Succ highest - 0) % Succ highest + Succ n) / Succ highest
  | Zero,   n => rewrite Nat.divOne n
  | Succ t, n =>
    calc Bool.toNat (Succ t == 0) + ((Succ (Succ t) - Succ t) % Succ (Succ t) + n) / Succ (Succ t)
      _ = (1 % Succ (Succ t) + n) / Succ (Succ t)  := rewrite Nat.succSub t
      _ = (1 + n) / Succ (Succ t)
      _ = ((Succ (Succ t) - 0) % Succ (Succ t) + Succ n) / Succ (Succ t) := rewrite Nat.modSelf (Succ (Succ t))

theorem stepLeft (highest: Nat): (a: Nat) -> a <= highest -> (n: Nat) ->
    Bool.toNat (place highest (Int.subNatNat a 1) == 0)
        + ((Succ highest - place highest (Int.subNatNat a 1)) % Succ highest + n) / Succ highest
      = ((Succ highest - a) % Succ highest + Succ n) / Succ highest
  | Zero,   h, n =>
    rewrite leftZero highest in stepLeftTop highest n
  | Succ m, h, n =>
    rewrite leftOne highest m h in stepLeftFrom highest m h n

theorem leftCount [n: Nat] (d: Mod n): (k: Nat) ->
    zerosAfter d (List.replicate k (Left 1)) = ((Mod.size n - d.value) % Mod.size n + k) / Mod.size n
  | Zero   =>
    rewrite Nat.addZero ((Mod.size n - d.value) % Mod.size n),
        Nat.divSmall ((Mod.size n - d.value) % Mod.size n) (Mod.size n)
          (Nat.modLt (Mod.size n - d.value) (Mod.size n))
  | Succ k =>
    calc zerosAfter d (List.replicate (Succ k) (Left 1))
      _ = Bool.toNat (place (n - 1) (Int.subNatNat d.value 1) == 0)
            + ((Mod.size n - place (n - 1) (Int.subNatNat d.value 1)) % Mod.size n + k) / Mod.size n
          := rewrite List.scanLeftCons move (move d (Left 1)) (List.replicate k (Left 1)), leftCount (move d (Left 1)) k, Mod.valueOfInt (d.toInt - Nat.toInt 1)
      _ = ((Mod.size n - d.value) % Mod.size n + Succ k) / Mod.size n := stepLeft (n - 1) d.value d.isLt k

-- A turn is its clicks, one at a time: it ends in the same place, and
-- `zerosDuring` counts the clicks that land on 0.
theorem turnAt [n: Nat] (d: Mod n): (t: Turn) -> List.foldLeft move d t.clicks = move d t
  | Left k  =>
    Mod.ext (List.foldLeft move d (Left k).clicks) (move d (Left k))
      (Eq.trans (leftAt d k) (Eq.sym (Mod.valueOfInt (d.toInt - k.toInt))))
  | Right k =>
    Mod.ext (List.foldLeft move d (Right k).clicks) (move d (Right k))
      (Eq.trans (rightAt d k) (Eq.sym (Mod.valueOfInt (d.toInt + k.toInt))))

theorem turnCount [n: Nat] (d: Mod n): (t: Turn) -> zerosAfter d t.clicks = zerosDuring d t
  | Left k  => leftCount d k
  | Right k => rightCount d k
