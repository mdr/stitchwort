-- Day 1, part 2 proved correct: the arithmetic count of the clicks that land on
-- 0 agrees with turning the dial one click at a time, for a dial of any size.
-- Kept apart from the program, so `stitchwort run Aoc.Day01.main` doesn't
-- check it.
--
-- The lemmas about the dial are for a dial of any size, `Succ highest`; with
-- the literal 100, `x % 100` unfolds to `x - 100 * (x / 100)` and `100 * q`
-- to a hundred additions, so every comparison of such types took seconds.

namespace Aoc.Day01.Proofs
import Aoc.Day01 (..)
import Std (Bool, Eq, Int, List, Nat)

-- The specification of part 2: turn the dial one click at a time, and count
-- the positions after each click that are 0.
def zerosPassedSpec (start: Dial highest) (turns: List Turn): Nat :=
  turns |> .concatMap Turn.clicks |> zerosLandedOn start

test "example, click by click" := zerosPassedSpec dial (parseTurns example) == 6

-- The zeros after each turn from `d`, counted by `List.occurrences`, which
-- suits proofs (it recurses on the list).
def zerosAfter (d: Dial highest) (turns: List Turn): Nat :=
  List.occurrences Dial.isZero (List.drop 1 (List.scanLeft Dial.move d turns))

-- The clicks of one turn, then the rest.
theorem zerosPassedSplit (d: Dial highest) (t: Turn) (ts: List Turn):
    zerosAfter d (t.clicks ++ List.concatMap Turn.clicks ts)
      = d.zerosDuring t + zerosAfter (d.move t) (List.concatMap Turn.clicks ts) :=
  calc zerosAfter d (t.clicks ++ List.concatMap Turn.clicks ts)
    _ = zerosAfter d t.clicks + zerosAfter (List.foldLeft Dial.move d t.clicks) (List.concatMap Turn.clicks ts)
        := Eq.trans (Eq.cong (List.occurrences Dial.isZero) (List.scanLeftAppend Dial.move d t.clicks (List.concatMap Turn.clicks ts)))
             (List.occurrencesAppend Dial.isZero _ _)
    _ = d.zerosDuring t + zerosAfter (List.foldLeft Dial.move d t.clicks) (List.concatMap Turn.clicks ts) := rewrite turnCount d t
    _ = d.zerosDuring t + zerosAfter (d.move t) (List.concatMap Turn.clicks ts)                          := rewrite turnAt d t

theorem zerosPassedFrom (d: Dial highest): (ts: List Turn) ->
    zerosPassed d ts = zerosAfter d (List.concatMap Turn.clicks ts)
  | Nil       => rfl
  | Cons t ts =>
    calc zerosPassed d (Cons t ts)
      _ = d.zerosDuring t + zerosPassed (d.move t) ts
          := List.sumCons (d.zerosDuring t) (List.zipWith Dial.zerosDuring (List.scanLeft Dial.move (d.move t) ts) ts)
      _ = d.zerosDuring t + zerosAfter (d.move t) (List.concatMap Turn.clicks ts) := rewrite zerosPassedFrom (d.move t) ts
      _ = zerosAfter d (List.concatMap Turn.clicks (Cons t ts))                   := Eq.sym (zerosPassedSplit d t ts)

-- Positions stay on the dial by the type `Dial` (its `inRange` field), and
-- part 1's code reads as the puzzle's own statement, so neither needs a
-- theorem. The theorem, `zerosPassedCorrect`, says the arithmetic count
-- `zerosDuring` agrees with turning the dial one click at a time, for any
-- dial, start and turns. The lemmas it rests on follow the definitions they
-- are about.

-- The arithmetic count is the click-by-click count, for any dial,
-- start and turns.
theorem zerosPassedCorrect (start: Dial highest) (turns: List Turn): zerosPassed start turns = zerosPassedSpec start turns :=
  Eq.trans (zerosPassedFrom start turns)
    (Eq.sym (List.countOccurrences Dial.isZero (List.drop 1 (List.scanLeft Dial.move start (List.concatMap Turn.clicks turns)))))

-- And so for the puzzle's answer.
theorem part2Puzzle (turns: List Turn): solvePart2 turns = zerosPassedSpec dial turns :=
  zerosPassedCorrect dial turns

-- Two dials at the same position are the same.
theorem dialExt: (d: Dial highest) -> (e: Dial highest) -> d.position = e.position -> d = e
  | { position = a, inRange = h1 }, { position = b, inRange = h2 }, e => dialExtAt highest a h1 b e h2

theorem dialExtAt (highest: Nat) (a: Nat) (h1: a <= highest) (b: Nat) (e: a = b): (h2: b <= highest) ->
    ({ position = a, inRange = h1 }: Dial highest) = { position = b, inRange = h2 } :=
  J (y e2 => (h3: y <= highest) -> ({ position = a, inRange = h1 }: Dial highest) = { position = y, inRange = h3 })
    (h3 => J (h e3 => ({ position = a, inRange = h1 }: Dial highest) = { position = a, inRange = h }) rfl (Bool.uniqueEq (Nat.leq a highest) True h1 h3))
    e

-- The lemmas about the dial are for a dial of any size, `Succ highest`: with
-- the literal 100, `x % 100` unfolds to `x - 100 * (x / 100)`, and `100 * q`
-- to a hundred additions, so every comparison of such types took seconds.
-- With a variable size the multiplication stays as it is.

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

theorem rightAt [highest: Nat] (d: Dial highest): (n: Nat) ->
    (List.foldLeft Dial.move d (List.replicate n (Right 1))).position = (d.position + n) % Succ highest
  | Zero   => rewrite Nat.addZero d.position, Nat.modSmall d.position (Succ highest) d.inRange
  | Succ n => Eq.trans (rightAt (d.move (Right 1)) n) (stepRightAt (Succ highest) d.position n)

-- Where an integer lands on a dial numbered 0 to `highest`. Proofs only: it
-- keeps `Int.modNat` folded, which the checker would otherwise unfold in the
-- lemmas below.
def place (highest: Nat) (x: Int): Nat := Int.modNat x (Succ highest)

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

theorem leftAt [highest: Nat] (d: Dial highest): (n: Nat) ->
    (List.foldLeft Dial.move d (List.replicate n (Left 1))).position = place highest (Nat.toInt d.position - Nat.toInt n)
  | Zero   => rewrite Nat.addZero d.position, Nat.modSmall d.position (Succ highest) d.inRange
  | Succ n => Eq.trans (leftAt (d.move (Left 1)) n) (stepLeftAt highest d.position d.inRange n)

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

theorem rightCount [highest: Nat] (d: Dial highest): (n: Nat) ->
    zerosAfter d (List.replicate n (Right 1)) = (d.position + n) / Succ highest
  | Zero   => rewrite Nat.addZero d.position, Nat.divSmall d.position (Succ highest) d.inRange
  | Succ n =>
    calc zerosAfter d (List.replicate (Succ n) (Right 1))
      _ = Bool.toNat (d.move (Right 1)).isZero + zerosAfter (d.move (Right 1)) (List.replicate n (Right 1))
          := Eq.cong (List.occurrences Dial.isZero) (List.scanLeftCons Dial.move (d.move (Right 1)) (List.replicate n (Right 1)))
      _ = Bool.toNat (d.move (Right 1)).isZero + ((d.move (Right 1)).position + n) / Succ highest
          := rewrite rightCount (d.move (Right 1)) n
      _ = (d.position + Succ n) / Succ highest := stepRight (Succ highest) d.position d.inRange n

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

theorem leftCount [highest: Nat] (d: Dial highest): (n: Nat) ->
    zerosAfter d (List.replicate n (Left 1)) = ((Succ highest - d.position) % Succ highest + n) / Succ highest
  | Zero   =>
    rewrite Nat.addZero ((Succ highest - d.position) % Succ highest),
        Nat.divSmall ((Succ highest - d.position) % Succ highest) (Succ highest) (Nat.modLt (Succ highest - d.position) (Succ highest))
  | Succ n =>
    calc zerosAfter d (List.replicate (Succ n) (Left 1))
      _ = Bool.toNat (d.move (Left 1)).isZero + zerosAfter (d.move (Left 1)) (List.replicate n (Left 1))
          := Eq.cong (List.occurrences Dial.isZero) (List.scanLeftCons Dial.move (d.move (Left 1)) (List.replicate n (Left 1)))
      _ = Bool.toNat (d.move (Left 1)).isZero + ((Succ highest - (d.move (Left 1)).position) % Succ highest + n) / Succ highest
          := rewrite leftCount (d.move (Left 1)) n
      _ = ((Succ highest - d.position) % Succ highest + Succ n) / Succ highest := stepLeft highest d.position d.inRange n

-- A turn is its clicks, one at a time: it ends in the same place, and
-- `zerosDuring` counts the clicks that land on 0.
theorem turnAt (d: Dial highest): (t: Turn) -> List.foldLeft Dial.move d t.clicks = d.move t
  | Left n  => dialExt (List.foldLeft Dial.move d (Left n).clicks) (d.move (Left n)) (leftAt d n)
  | Right n => dialExt (List.foldLeft Dial.move d (Right n).clicks) (d.move (Right n)) (rightAt d n)

theorem turnCount (d: Dial highest): (t: Turn) -> zerosAfter d t.clicks = d.zerosDuring t
  | Left n  => leftCount d n
  | Right n => rightCount d n
