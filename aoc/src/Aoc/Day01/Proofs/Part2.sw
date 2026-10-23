-- Day 1, part 2 proved correct: the arithmetic count of the clicks that land on
-- 0 agrees with turning the dial one click at a time, for a dial of any size.
-- Kept apart from the program, so `stitchwort run Aoc.Day01.main` doesn't
-- check it.
--
-- The lemmas about the dial are for a dial of any size, `Mod n`, not just the
-- puzzle's 100: the proof then says nothing about the particular number, and
-- the theorem covers every dial.

namespace Aoc.Day01.Proofs
import Aoc.Day01 (..)
import Aoc.Day01.Tests (example)
import Std (Bool, Eq, Int, List, Mod, Nat)

-- The specification of part 2: turn the dial one click at a time, and count
-- the positions after each click that are 0.
def zerosPassedSpec (startingDial: Dial n) (turns: List Turn): Nat :=
  turns |> .concatMap Turn.clicks |> zerosLandedOn startingDial

test "example, click by click" := zerosPassedSpec startingDial (parseTurns example) == 6

-- The zeros after each turn from `dial`, counted by `List.occurrences`, which
-- suits proofs (it recurses on the list).
def zerosAfter (dial: Dial n) (turns: List Turn): Nat :=
  List.occurrences Dial.isZero (List.drop 1 (List.scanLeft Dial.move dial turns))

-- The clicks of one turn, then the rest.
theorem zerosPassedSplit [n: Nat] (dial: Dial n) (t: Turn) (ts: List Turn):
    zerosAfter dial (t.clicks ++ List.concatMap Turn.clicks ts)
      = Dial.zerosDuring dial t + zerosAfter (Dial.move dial t) (List.concatMap Turn.clicks ts) :=
  calc zerosAfter dial (t.clicks ++ List.concatMap Turn.clicks ts)
    _ = zerosAfter dial t.clicks + zerosAfter (List.foldLeft Dial.move dial t.clicks) (List.concatMap Turn.clicks ts)
        := Eq.trans (Eq.cong (List.occurrences Dial.isZero) (List.scanLeftAppend Dial.move dial t.clicks (List.concatMap Turn.clicks ts)))
             (List.occurrencesAppend Dial.isZero _ _)
    _ = Dial.zerosDuring dial t + zerosAfter (List.foldLeft Dial.move dial t.clicks) (List.concatMap Turn.clicks ts) := rewrite turnCount dial t
    _ = Dial.zerosDuring dial t + zerosAfter (Dial.move dial t) (List.concatMap Turn.clicks ts)                      := rewrite turnAt dial t

theorem zerosPassedFrom [n: Nat] (dial: Dial n): (ts: List Turn) ->
    zerosPassed dial ts = zerosAfter dial (List.concatMap Turn.clicks ts)
  | Nil       => rfl
  | Cons t ts =>
    calc zerosPassed dial (Cons t ts)
      _ = Dial.zerosDuring dial t + zerosPassed (Dial.move dial t) ts
          := List.sumCons (Dial.zerosDuring dial t) (List.zipWith Dial.zerosDuring (List.scanLeft Dial.move (Dial.move dial t) ts) ts)
      _ = Dial.zerosDuring dial t + zerosAfter (Dial.move dial t) (List.concatMap Turn.clicks ts) := rewrite zerosPassedFrom (Dial.move dial t) ts
      _ = zerosAfter dial (List.concatMap Turn.clicks (Cons t ts))                   := Eq.sym (zerosPassedSplit dial t ts)

-- Positions stay on the dial by the type `Mod n`, and part 1's code reads as
-- the puzzle's own statement, so neither needs a theorem. The theorem,
-- `zerosPassedCorrect`, says the arithmetic count `Dial.zerosDuring` agrees with
-- turning the dial one click at a time, for any dial, start and turns. The
-- lemmas it rests on follow the definitions they are about.

-- The arithmetic count is the click-by-click count, for any dial,
-- start and turns.
theorem zerosPassedCorrect [n: Nat] (startingDial: Dial n) (turns: List Turn): zerosPassed startingDial turns = zerosPassedSpec startingDial turns :=
  Eq.trans (zerosPassedFrom startingDial turns)
    (Eq.sym (List.countOccurrences Dial.isZero (List.drop 1 (List.scanLeft Dial.move startingDial (List.concatMap Turn.clicks turns)))))

-- And so for the puzzle's answer.
theorem part2Puzzle (turns: List Turn): solvePart2 turns = zerosPassedSpec startingDial turns :=
  zerosPassedCorrect startingDial turns

-- The lemmas below are about a dial with `Succ highest` positions, which is
-- what `Mod.size n` is (with `highest` as `n - 1`).

-- Where an integer lands on a dial numbered 0 to `highest`. Proofs only: it
-- keeps `Int.modNat` folded, which the checker would otherwise unfold in the
-- lemmas below.
def place (highest: Nat) (x: Int): Nat := Int.modNat x (Succ highest)

theorem stepRightAt (d: Nat) [auto ok: d != 0] (a: Nat) (n: Nat):
    ((a + 1) % d + n) % d = (a + Succ n) % d :=
  calc ((a + 1) % d + n) % d
    _ = (a + 1 + n) % d  := Nat.modAddMod (a + 1) n d
    _ = (a + Succ n) % d := rewrite Nat.addAssoc a 1 n

theorem rightAt [n: Nat] (dial: Dial n): (k: Nat) ->
    (List.foldLeft Dial.move dial (List.replicate k (Right 1))).position.value = (dial.position.value + k) % Mod.size n
  | Zero   => rewrite Nat.addZero dial.position.value, Nat.modSmall dial.position.value (Mod.size n) dial.position.isLt
  | Succ k =>
    rewrite rightAt (Dial.move dial (Right 1)) k, Mod.valueOfInt (dial.position.toInt + Nat.toInt 1) in stepRightAt (Mod.size n) dial.position.value k

-- One click left: from 0 to `highest`, otherwise down by one.
theorem leftZero (highest: Nat): place highest (Int.subNatNat 0 1) = highest := Int.modNatNegOne highest

theorem leftOne (highest: Nat) (m: Nat) (h: Succ m <= highest): place highest (Int.subNatNat (Succ m) 1) = m :=
  calc place highest (Int.subNatNat (Succ m) 1)
    _ = place highest (OfNat m) := Eq.cong (x => place highest x) (Eq.trans (Int.subNatNatSucc m 0) (Int.subNatNatZeroRight m))
    _ = m := Nat.modSmall m (Succ highest) omega

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

theorem leftAt [n: Nat] (dial: Dial n): (k: Nat) ->
    (List.foldLeft Dial.move dial (List.replicate k (Left 1))).position.value = place (n - 1) (Nat.toInt dial.position.value - Nat.toInt k)
  | Zero   => rewrite Nat.addZero dial.position.value, Nat.modSmall dial.position.value (Mod.size n) dial.position.isLt
  | Succ k =>
    rewrite leftAt (Dial.move dial (Left 1)) k, Mod.valueOfInt (dial.position.toInt - Nat.toInt 1) in stepLeftAt (n - 1) dial.position.value dial.position.isLt k

theorem stepRight (d: Nat) [auto ok: d != 0] (a: Nat) (h: a < d) (n: Nat):
    Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d = (a + Succ n) / d :=
  match e: Nat.leq d (Succ a) with
    | True  =>
      -- the click wraps: `a + 1 = d`, so the dial goes to 0
      calc Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d
        _ = Succ (n / d)       := rewrite (omega: a + 1 = d), Nat.modSelf d
        _ = (d + n) / d        := Eq.sym (Nat.addDivSelf d n)
        _ = (Succ a + n) / d   := Eq.cong (x => (x + n) / d) (omega: d = Succ a)
        _ = (a + Succ n) / d   := rewrite Nat.addSucc a n
    | False =>
      -- no wrap: `Succ a < d`, so the dial goes to `a + 1`
      rewrite Nat.addOne a, Nat.modSmall (Succ a) d (omega: Succ a < d), Nat.addSucc a n

theorem rightCount [n: Nat] (dial: Dial n): (k: Nat) ->
    zerosAfter dial (List.replicate k (Right 1)) = (dial.position.value + k) / Mod.size n
  | Zero   => rewrite Nat.addZero dial.position.value, Nat.divSmall dial.position.value (Mod.size n) dial.position.isLt
  | Succ k =>
    calc zerosAfter dial (List.replicate (Succ k) (Right 1))
      _ = Bool.toNat ((dial.position.value + 1) % Mod.size n == 0) + ((dial.position.value + 1) % Mod.size n + k) / Mod.size n
          := rewrite List.scanLeftCons Dial.move (Dial.move dial (Right 1)) (List.replicate k (Right 1)), rightCount (Dial.move dial (Right 1)) k, Mod.valueOfInt (dial.position.toInt + Nat.toInt 1)
      _ = (dial.position.value + Succ k) / Mod.size n := stepRight (Mod.size n) dial.position.value dial.position.isLt k

-- The count after one click left to `m`, from `Succ m`.
theorem stepLeftFrom (highest: Nat): (m: Nat) -> Succ m <= highest -> (n: Nat) ->
    Bool.toNat (m == 0) + ((Succ highest - m) % Succ highest + n) / Succ highest
      = ((Succ highest - Succ m) % Succ highest + Succ n) / Succ highest
  | Zero,   h, n =>
    rewrite Nat.modSelf (Succ highest), Nat.modSmall highest (Succ highest) omega, Nat.addSucc highest n
      in Eq.sym (Nat.addDivSelf (Succ highest) n)
  | Succ j, h, n =>
    rewrite Nat.modSmall (highest - j) (Succ highest) omega,
        Nat.modSmall (highest - Succ j) (Succ highest) omega,
        (omega: highest - j = Succ (highest - Succ j)),
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

theorem leftCount [n: Nat] (dial: Dial n): (k: Nat) ->
    zerosAfter dial (List.replicate k (Left 1)) = ((Mod.size n - dial.position.value) % Mod.size n + k) / Mod.size n
  | Zero   =>
    rewrite Nat.addZero ((Mod.size n - dial.position.value) % Mod.size n),
        Nat.divSmall ((Mod.size n - dial.position.value) % Mod.size n) (Mod.size n)
          (Nat.modLt (Mod.size n - dial.position.value) (Mod.size n))
  | Succ k =>
    calc zerosAfter dial (List.replicate (Succ k) (Left 1))
      _ = Bool.toNat (place (n - 1) (Int.subNatNat dial.position.value 1) == 0)
            + ((Mod.size n - place (n - 1) (Int.subNatNat dial.position.value 1)) % Mod.size n + k) / Mod.size n
          := rewrite List.scanLeftCons Dial.move (Dial.move dial (Left 1)) (List.replicate k (Left 1)), leftCount (Dial.move dial (Left 1)) k, Mod.valueOfInt (dial.position.toInt - Nat.toInt 1)
      _ = ((Mod.size n - dial.position.value) % Mod.size n + Succ k) / Mod.size n := stepLeft (n - 1) dial.position.value dial.position.isLt k

-- A turn is its clicks, one at a time: it ends in the same place, and
-- `Dial.zerosDuring` counts the clicks that land on 0.
theorem turnAt [n: Nat] (dial: Dial n): (t: Turn) -> List.foldLeft Dial.move dial t.clicks = Dial.move dial t
  | Left k  =>
    Dial.ext (List.foldLeft Dial.move dial (Left k).clicks) (Dial.move dial (Left k))
      (Mod.ext _ _ (Eq.trans (leftAt dial k) (Eq.sym (Mod.valueOfInt (dial.position.toInt - k.toInt)))))
  | Right k =>
    Dial.ext (List.foldLeft Dial.move dial (Right k).clicks) (Dial.move dial (Right k))
      (Mod.ext _ _ (Eq.trans (rightAt dial k) (Eq.sym (Mod.valueOfInt (dial.position.toInt + k.toInt)))))

theorem turnCount [n: Nat] (dial: Dial n): (t: Turn) -> zerosAfter dial t.clicks = Dial.zerosDuring dial t
  | Left k  => leftCount dial k
  | Right k => rightCount dial k
