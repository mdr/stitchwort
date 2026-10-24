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
import Aoc.Day01.Spec (..)
import Std (Bool, Eq, Fail, Int, List, Mod, Nat)

-- The zeros after the first turn, then after the rest.
theorem zerosLandedOnCons [n: Nat] (dial: Dial n) (t: Turn) (ts: List Turn):
    zerosLandedOn dial (Cons t ts) = Bool.toNat (Dial.isZero (Dial.move dial t)) + zerosLandedOn (Dial.move dial t) ts :=
  Eq.trans (Eq.cong (List.count Dial.isZero) (List.scanLeftCons Dial.move (Dial.move dial t) ts))
    (List.countCons Dial.isZero (Dial.move dial t) (List.drop 1 (List.scanLeft Dial.move (Dial.move dial t) ts)))

-- The clicks of one turn, then the rest.
theorem zerosPassedSplit [n: Nat] (dial: Dial n) (t: Turn) (ts: List Turn):
    zerosLandedOn dial (t.clicks ++ List.concatMap Turn.clicks ts)
      = Dial.zerosDuring dial t + zerosLandedOn (Dial.move dial t) (List.concatMap Turn.clicks ts) :=
  calc zerosLandedOn dial (t.clicks ++ List.concatMap Turn.clicks ts)
    _ = zerosLandedOn dial t.clicks + zerosLandedOn (List.foldLeft Dial.move dial t.clicks) (List.concatMap Turn.clicks ts)
      := Eq.trans (Eq.cong (List.count Dial.isZero) (List.scanLeftAppend Dial.move dial t.clicks (List.concatMap Turn.clicks ts)))
        (List.countAppend Dial.isZero _ _)
    _ = Dial.zerosDuring dial t + zerosLandedOn (List.foldLeft Dial.move dial t.clicks) (List.concatMap Turn.clicks ts) := rewrite turnCount dial t
    _ = Dial.zerosDuring dial t + zerosLandedOn (Dial.move dial t) (List.concatMap Turn.clicks ts) := rewrite turnAt dial t

theorem zerosPassedFrom [n: Nat] (dial: Dial n): (ts: List Turn) ->
    zerosPassed dial ts = zerosLandedOn dial (List.concatMap Turn.clicks ts)
  | Nil => rfl
  | Cons t ts =>
    calc zerosPassed dial (Cons t ts)
      _ = Dial.zerosDuring dial t + zerosPassed (Dial.move dial t) ts
        := List.sumCons (Dial.zerosDuring dial t) (List.zipWith Dial.zerosDuring (List.scanLeft Dial.move (Dial.move dial t) ts) ts)
      _ = Dial.zerosDuring dial t + zerosLandedOn (Dial.move dial t) (List.concatMap Turn.clicks ts) := rewrite zerosPassedFrom (Dial.move dial t) ts
      _ = zerosLandedOn dial (List.concatMap Turn.clicks (Cons t ts)) := Eq.sym (zerosPassedSplit dial t ts)

-- Positions stay on the dial by the type `Mod n`, and part 1's code reads as
-- the puzzle's own statement, so neither needs a theorem. The theorem,
-- `zerosPassedCorrect`, says the arithmetic count `Dial.zerosDuring` agrees with
-- turning the dial one click at a time, for any dial, start and turns. The
-- lemmas it rests on follow the definitions they are about.

-- The arithmetic count is the click-by-click count, for any dial,
-- start and turns.
theorem zerosPassedCorrect [n: Nat] (startingDial: Dial n) (turns: List Turn): zerosPassed startingDial turns = zerosPassedSpec startingDial turns :=
  zerosPassedFrom startingDial turns

-- And so for the puzzle's answer.
theorem part2Puzzle (turns: List Turn): solvePart2 turns = zerosPassedSpec startingDial turns :=
  zerosPassedCorrect startingDial turns

-- A turn ends where its clicks, one at a time, do: moving by 1 and then by `k`
-- is moving by `1 + k`, which is `Succ k`.
theorem rightAt [n: Nat] (dial: Dial n): (k: Nat) ->
    List.foldLeft Dial.move dial (List.replicate k (Right 1)) = Dial.move dial (Right k)
  | Zero => Dial.ext dial (Dial.move dial (Right 0)) (Eq.sym (Mod.addNatZero dial.position))
  | Succ k =>
    Eq.trans (rightAt (Dial.move dial (Right 1)) k)
      (Dial.ext (Dial.move (Dial.move dial (Right 1)) (Right k)) (Dial.move dial (Right (Succ k))) (Mod.addNatAddNat dial.position 1 k))

theorem leftAt [n: Nat] (dial: Dial n): (k: Nat) ->
    List.foldLeft Dial.move dial (List.replicate k (Left 1)) = Dial.move dial (Left k)
  | Zero => Dial.ext dial (Dial.move dial (Left 0)) (Eq.sym (Mod.subNatZero dial.position))
  | Succ k =>
    Eq.trans (leftAt (Dial.move dial (Left 1)) k)
      (Dial.ext (Dial.move (Dial.move dial (Left 1)) (Left k)) (Dial.move dial (Left (Succ k))) (Mod.subNatSubNat dial.position 1 k))

theorem stepRight (d: Nat) [auto ok: d != 0] (a: Nat) (h: a < d) (n: Nat):
    Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d = (a + Succ n) / d :=
  match e: Nat.leq d (Succ a) with
    | True =>
      -- the click wraps: `a + 1 = d`, so the dial goes to 0
      calc Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d
        _ = Succ (n / d) := rewrite (omega: a + 1 = d), Nat.modSelf d
        _ = (d + n) / d := Eq.sym (Nat.addDivSelf d n)
        _ = (Succ a + n) / d := rewrite (omega: d = Succ a)
        _ = (a + Succ n) / d := rewrite (ring: a + Succ n = Succ a + n)
    | False =>
      -- no wrap: `Succ a < d`, so the dial goes to `a + 1`
      rewrite Nat.addOne a, Nat.modSmall (Succ a) d (omega: Succ a < d), Nat.addSucc a n

theorem rightCount [n: Nat] (dial: Dial n): (k: Nat) ->
    zerosLandedOn dial (List.replicate k (Right 1)) = (dial.position.value + k) / Mod.size n
  | Zero => rewrite Nat.addZero dial.position.value, Nat.divSmall dial.position.value (Mod.size n) dial.position.isLt
  | Succ k =>
    calc zerosLandedOn dial (List.replicate (Succ k) (Right 1))
      _ = Bool.toNat ((dial.position.value + 1) % Mod.size n == 0) + ((dial.position.value + 1) % Mod.size n + k) / Mod.size n
        := rewrite zerosLandedOnCons dial (Right 1) (List.replicate k (Right 1)), rightCount (Dial.move dial (Right 1)) k, Mod.valueOfInt (dial.position.toInt + Nat.toInt 1)
      _ = (dial.position.value + Succ k) / Mod.size n := stepRight (Mod.size n) dial.position.value dial.position.isLt k

-- Going left is going right in a mirror (`Dial.zerosDuring`): the dial at
-- `Mod.neg` of its position, where 0 stays put.
def mirror (dial: Dial n): Dial n := { position = Mod.neg dial.position }

-- The mirror is at 0 exactly when the dial is.
theorem isZeroNeg (m: Nat): (v: Nat) -> v < Succ m -> ((Succ m - v) % Succ m == 0) = (v == 0)
  | Zero, h => rewrite Nat.modSelf (Succ m)
  | Succ w, h => rewrite Nat.modSmall (m - w) (Succ m) omega, (omega: m - w = Succ (m - Succ w))

theorem mirrorIsZero [n: Nat] (dial: Dial n): Dial.isZero (mirror dial) = Dial.isZero dial :=
  rewrite Mod.valueNeg dial.position in isZeroNeg (n - 1) dial.position.value dial.position.isLt

-- One click left, mirrored, is one click right from the mirror.
theorem mirrorLeft [n: Nat] (dial: Dial n): mirror (Dial.move dial (Left 1)) = Dial.move (mirror dial) (Right 1) :=
  Dial.ext (mirror (Dial.move dial (Left 1))) (Dial.move (mirror dial) (Right 1)) (Mod.negSubNat dial.position 1)

theorem leftMirror [n: Nat] (dial: Dial n): (k: Nat) ->
    zerosLandedOn dial (List.replicate k (Left 1)) = zerosLandedOn (mirror dial) (List.replicate k (Right 1))
  | Zero => rfl
  | Succ k =>
    calc zerosLandedOn dial (List.replicate (Succ k) (Left 1))
      _ = Bool.toNat (Dial.isZero (Dial.move dial (Left 1))) + zerosLandedOn (mirror (Dial.move dial (Left 1))) (List.replicate k (Right 1))
        := rewrite zerosLandedOnCons dial (Left 1) (List.replicate k (Left 1)), leftMirror (Dial.move dial (Left 1)) k
      _ = Bool.toNat (Dial.isZero (mirror (Dial.move dial (Left 1)))) + zerosLandedOn (mirror (Dial.move dial (Left 1))) (List.replicate k (Right 1))
        := rewrite mirrorIsZero (Dial.move dial (Left 1))
      _ = zerosLandedOn (mirror dial) (List.replicate (Succ k) (Right 1))
        := Eq.trans (Eq.cong (d => Bool.toNat (Dial.isZero d) + zerosLandedOn d (List.replicate k (Right 1))) (mirrorLeft dial))
          (Eq.sym (zerosLandedOnCons (mirror dial) (Right 1) (List.replicate k (Right 1))))

-- A turn is its clicks, one at a time: it ends in the same place, and
-- `Dial.zerosDuring` counts the clicks that land on 0.
theorem turnAt [n: Nat] (dial: Dial n): (t: Turn) -> List.foldLeft Dial.move dial t.clicks = Dial.move dial t
  | Left k => leftAt dial k
  | Right k => rightAt dial k

theorem turnCount [n: Nat] (dial: Dial n): (t: Turn) -> zerosLandedOn dial t.clicks = Dial.zerosDuring dial t
  | Left k =>
    Eq.trans (leftMirror dial k)
      (Eq.trans (rightCount (mirror dial) k) (Eq.cong (v => (v + k) / Mod.size n) (Mod.valueNeg dial.position)))
  | Right k => rightCount dial k
