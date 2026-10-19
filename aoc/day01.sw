-- Advent of Code 2025, day 1: a dial numbered 0 to 99 starts at 50 and is
-- turned left or right. Part 1 counts the turns that end on 0; part 2 counts
-- every click that lands on 0, including those in the middle of a turn.
--
--   $ stitchwort run aoc/day01.sw < aoc/inputs/day01.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- The dial's size is a parameter, `highest` being its largest number (99 in
-- the puzzle). The proofs below are about any dial; besides being more
-- general, that keeps them fast to check (see "Proofs" below).

def main (): {IO} () :=
  let turns := parseTurns (IO.readAllLines ())
  print "Part 1: ${solvePart1 turns}"
  print "Part 2: ${solvePart2 turns}"

def parseTurns (lines: List Text): List Turn := lines.mapMaybe Turn.parse

def solvePart1 (turns: List Turn): Nat := zerosLandedOn dial turns

def solvePart2 (turns: List Turn): Nat := zerosPassed dial turns

-- The puzzle's dial, at 50.
def dial: Dial 99 := { position = 50, inRange = rfl }

-- Part 1: the positions after each turn that are 0.
def zerosLandedOn (start: Dial highest) (turns: List Turn): Nat :=
  turns
    |> .scanLeft Dial.move start
    |> .drop 1
    |> .count Dial.isZero

-- Part 2: for each turn, the clicks onto 0 from where the dial was before it.
def zerosPassed (start: Dial highest) (turns: List Turn): Nat :=
  turns
    |> .scanLeft Dial.move start
    |> .zipWith Dial.zerosDuring turns
    |> .sum

-- The specification of part 2: turn the dial one click at a time, and count
-- the positions after each click that are 0.
def zerosPassedSpec (start: Dial highest) (turns: List Turn): Nat :=
  turns |> .concatMap Turn.clicks |> zerosLandedOn start

type Turn =
  | Left (distance: Nat)
  | Right (distance: Nat)

-- "L68" is `Left 68`.
def Turn.parse (t: Text): Maybe Turn :=
  def turnOf (c: Char) (n: Nat): Maybe Turn :=
    match c with
      | 'L' => Just (Left n)
      | 'R' => Just (Right n)
      | _   => Nothing
  t.uncons.andThen (\(c, rest) => rest.toNat.andThen (turnOf c))

-- A turn, one click at a time: `Left 3` is three `Left 1`s.
def Turn.clicks: Turn -> List Turn
  | Left n  => List.replicate n (Left 1)
  | Right n => List.replicate n (Right 1)

-- A dial numbered 0 to `highest`, at `position`.
type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }

-- Any integer, wrapped onto the dial.
def Dial.fromInt (highest: Nat) (x: Int): Dial highest :=
  { position = Int.modNat x (Succ highest), inRange = Int.modNatLt x (Succ highest) }

-- The number of positions on the dial.
def Dial.size (d: Dial highest): Nat := Succ highest

-- Where a turn leaves the dial.
def Dial.move (d: Dial highest): Turn -> Dial highest
  | Left n  => Dial.fromInt highest (d.position.toInt - n.toInt)
  | Right n => Dial.fromInt highest (d.position.toInt + n.toInt)

def Dial.isZero (d: Dial highest): Bool := d.position == 0

-- How many clicks of a turn land on 0. Going right from `d`, the dial is at
-- 0 after each click that brings `d + k` to a multiple of the dial's size.
-- Going left is the mirror image: 0 is `(size - d) % size` clicks away.
def Dial.zerosDuring (d: Dial highest): Turn -> Nat
  | Right n => (d.position + n) / d.size
  | Left n  => ((d.size - d.position) % d.size + n) / d.size

-- Examples -----------------------------------------------------------------

def example: List Text := ["L68", "L30", "R48", "L5", "R60", "L55", "L1", "L99", "R14", "L82"]

def after (t: Text): Maybe Nat := (Turn.parse t).map (\turn => (dial.move turn).position)

def zerosFrom (x: Int) (t: Turn): Nat := (Dial.fromInt 99 x).zerosDuring t

test "example" := (solvePart1 (parseTurns example), solvePart2 (parseTurns example)) == (3, 6)
test "example, click by click" := zerosPassedSpec dial (parseTurns example) == 6
test "parse" := after "L68" == Just 82
test "parse right" := after "R5" == Just 55
test "parse junk" := after "X5" == Nothing
test "left past zero" := zerosFrom 10 (Left 40) == 1
test "left onto zero" := zerosFrom 20 (Left 20) == 1
test "right onto zero" := zerosFrom 0 (Right 100) == 1
test "left from zero" := zerosFrom 0 (Left 42) == 0
test "left a full turn from zero" := zerosFrom 0 (Left 200) == 2

-- Proofs ------------------------------------------------------------------
--
-- Theorem 1 (positions stay on the dial) holds by the type `Dial`, and part
-- 1 is its own specification (theorem 3, `part1Puzzle`). Theorem 2,
-- `zerosPassedCorrect`, says the arithmetic count `zerosDuring` agrees with
-- turning the dial one click at a time, for any dial, start and turns.
--
-- The lemmas are about a dial of any size, `Succ highest`: with the literal
-- 100, `x % 100` unfolds to `x - 100 * (x / 100)`, and `100 * q` to a
-- hundred additions, so every comparison of such types took seconds. With a
-- variable size the multiplication stays as it is.

-- Theorem 1: every position is on the dial, by its type.
theorem alwaysOnDial [highest: Nat] (d: Dial highest) (t: Turn): (d.move t).position <= highest := (d.move t).inRange

-- Theorem 2: the arithmetic count is the click-by-click count, for any dial,
-- start and turns.
theorem zerosPassedCorrect (start: Dial highest) (turns: List Turn): zerosPassed start turns = zerosPassedSpec start turns :=
  Eq.trans (zerosPassedFrom start turns)
    (Eq.sym (List.countOccurrences Dial.isZero (List.drop 1 (List.scanLeft Dial.move start (List.concatMap Turn.clicks turns)))))

-- And so for the puzzle's answer.
theorem part2Puzzle (turns: List Turn): solvePart2 turns = zerosPassedSpec dial turns :=
  zerosPassedCorrect dial turns

-- Theorem 3: part 1 is the count of the positions after each turn that are 0.
theorem part1Puzzle (turns: List Turn):
    solvePart1 turns = ((List.scanLeft Dial.move dial turns).drop 1).count Dial.isZero := rfl

-- The zeros after each turn from `d`, counted by `List.occurrences`, which
-- suits proofs (it recurses on the list).
def zerosAfter (d: Dial highest) (turns: List Turn): Nat :=
  List.occurrences Dial.isZero (List.drop 1 (List.scanLeft Dial.move d turns))

-- Integers.
theorem subNatNatFromSucc (m: Nat) (n: Nat): (k: Nat) -> Int.subNatNatFrom (Succ m) (Succ n) k = Int.subNatNatFrom m n k
  | Zero   => rfl
  | Succ k => rfl

theorem subNatNatSucc (m: Nat) (n: Nat): Int.subNatNat (Succ m) (Succ n) = Int.subNatNat m n := subNatNatFromSucc m n (n - m)

theorem subNatNatZero (m: Nat): Int.subNatNat m 0 = Nat.toInt m := Eq.cong (\k => Int.subNatNatFrom m 0 k) (Nat.zeroSub m)

theorem subIsSubNatNat (m: Nat): (n: Nat) -> Nat.toInt m - Nat.toInt n = Int.subNatNat m n
  | Zero   => Eq.trans (Eq.cong Nat.toInt (Nat.addZero m)) (Eq.sym (subNatNatZero m))
  | Succ n => rfl

-- Two dials at the same position are the same.
theorem dialExt: (d: Dial highest) -> (e: Dial highest) -> d.position = e.position -> d = e
  | { position = a, inRange = h1 }, { position = b, inRange = h2 }, e => dialExtAt highest a h1 b e h2

theorem dialExtAt (highest: Nat) (a: Nat) (h1: a <= highest) (b: Nat) (e: a = b): (h2: b <= highest) ->
    ({ position = a, inRange = h1 }: Dial highest) = { position = b, inRange = h2 } :=
  J (\y e2 => (h3: y <= highest) -> ({ position = a, inRange = h1 }: Dial highest) = { position = y, inRange = h3 })
    (\h3 => J (\h e3 => ({ position = a, inRange = h1 }: Dial highest) = { position = a, inRange = h }) rfl (Bool.uniqueEq (Nat.leq a highest) True h1 h3))
    e

-- One click right on a dial of size `n`: from `a + 1 = n` the dial goes to
-- 0, otherwise to `a + 1`.
theorem rightCases (n: Nat) [auto ok: n != 0] (a: Nat) (h: a < n) (goal: Prop)
    (wraps: a + 1 = n -> goal) (below: Succ a < n -> goal): goal :=
  Bool.inspect (Nat.leq n (Succ a)) (\b => goal)
    (\t => wraps (Eq.trans (Nat.addOne a) (Nat.leAntisym (Succ a) n h t)))
    (\f => below (Nat.leqFalse n (Succ a) f))

theorem stepRightAt (d: Nat) [auto ok: d != 0] (a: Nat) (h: a < d) (n: Nat):
    ((a + 1) % d + n) % d = (a + Succ n) % d :=
  rightCases d a h (((a + 1) % d + n) % d = (a + Succ n) % d)
    (\e => Eq.trans (Eq.cong (\x => (x + n) % d) (Eq.trans (Eq.cong (\x => x % d) e) (Nat.modSelf d)))
      (Eq.sym (Eq.trans (Eq.cong (\x => x % d) (Eq.trans (Nat.addSucc a n) (Eq.cong (\x => x + n) (Eq.trans (Eq.sym (Nat.addOne a)) e))))
        (Nat.addModSelf d n))))
    (\lt => Eq.trans (Eq.cong (\x => (x + n) % d) (Eq.trans (Eq.cong (\x => x % d) (Nat.addOne a)) (Nat.modSmall (Succ a) d lt)))
      (Eq.cong (\x => x % d) (Eq.sym (Nat.addSucc a n))))

theorem stepRight (d: Nat) [auto ok: d != 0] (a: Nat) (h: a < d) (n: Nat):
    Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d = (a + Succ n) / d :=
  rightCases d a h (Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d = (a + Succ n) / d)
    (\e => Eq.trans (Eq.cong (\x => Bool.toNat (x == 0) + (x + n) / d) (Eq.trans (Eq.cong (\x => x % d) e) (Nat.modSelf d)))
      (Eq.sym (Eq.trans (Eq.cong (\x => x / d) (Eq.trans (Nat.addSucc a n) (Eq.cong (\x => x + n) (Eq.trans (Eq.sym (Nat.addOne a)) e))))
        (Nat.addDivSelf d n))))
    (\lt => Eq.trans (Eq.cong (\x => Bool.toNat (x == 0) + (x + n) / d) (Eq.trans (Eq.cong (\x => x % d) (Nat.addOne a)) (Nat.modSmall (Succ a) d lt)))
      (Eq.cong (\x => x / d) (Eq.sym (Nat.addSucc a n))))

theorem rightAt [highest: Nat] (d: Dial highest): (n: Nat) ->
    (List.foldLeft Dial.move d (List.replicate n (Right 1))).position = (d.position + n) % Succ highest
  | Zero   => Eq.sym (Eq.trans (Eq.cong (\x => x % Succ highest) (Nat.addZero d.position)) (Nat.modSmall d.position (Succ highest) d.inRange))
  | Succ n => Eq.trans (rightAt (d.move (Right 1)) n) (stepRightAt (Succ highest) d.position d.inRange n)

theorem rightCount [highest: Nat] (d: Dial highest): (n: Nat) ->
    zerosAfter d (List.replicate n (Right 1)) = (d.position + n) / Succ highest
  | Zero   => Eq.sym (Eq.trans (Eq.cong (\x => x / Succ highest) (Nat.addZero d.position)) (Nat.divSmall d.position (Succ highest) d.inRange))
  | Succ n =>
    Eq.trans (Eq.cong (List.occurrences Dial.isZero) (List.scanLeftCons Dial.move (d.move (Right 1)) (List.replicate n (Right 1))))
      (Eq.trans (Eq.cong (\t => Bool.toNat (d.move (Right 1)).isZero + t) (rightCount (d.move (Right 1)) n))
        (stepRight (Succ highest) d.position d.inRange n))

-- Where an integer lands on a dial numbered 0 to `highest`. Proofs only: it
-- keeps `Int.modNat` folded, which the checker would otherwise unfold in the
-- lemmas below.
def Dial.place (highest: Nat) (x: Int): Nat := Int.modNat x (Succ highest)

-- Going left from 0 on a dial of size `Succ m` ends at `m - n % Succ m`.
theorem backFrom (m: Nat) (n: Nat): Dial.place m (Int.subNatNat m n) = m - n % Succ m :=
  Bool.inspect (Nat.leq n m) (\b => Dial.place m (Int.subNatNat m n) = m - n % Succ m)
    (\h => Eq.trans (Eq.cong (\k => Dial.place m (Int.subNatNatFrom m n k)) (Nat.subEqZero n m h))
      (Eq.trans (Nat.modSmall (m - n) (Succ m) (Nat.subLe m n)) (Eq.sym (Eq.cong (\x => m - x) (Nat.modSmall n (Succ m) h)))))
    (\f => J (\y e => Dial.place m (Int.subNatNat m y) = m - y % Succ m)
      (backFar m (n - Succ m)) (Nat.addSubCancel (Succ m) n (Nat.leqFalse n m f)))

theorem backFar (m: Nat) (r: Nat): Dial.place m (Int.subNatNat m (Succ m + r)) = m - (Succ m + r) % Succ m :=
  Eq.trans (Eq.cong (\k => Dial.place m (Int.subNatNatFrom m (Succ m + r) k)) (Nat.succAddSub m r))
    (Eq.sym (Eq.cong (\x => m - x) (Nat.addModSelf (Succ m) r)))

-- One click left: from 0 to `highest`, otherwise down by one.
theorem leftZero (highest: Nat): Dial.place highest (Int.subNatNat 0 1) = highest :=
  Eq.cong (\x => highest - x) (Nat.modSmall 0 (Succ highest) rfl)

theorem leftOne (highest: Nat) (m: Nat) (h: Succ m <= highest): Dial.place highest (Int.subNatNat (Succ m) 1) = m :=
  Eq.trans (Eq.cong (\x => Dial.place highest x) (Eq.trans (subNatNatSucc m 0) (subNatNatZero m)))
    (Nat.modSmall m (Succ highest) (Nat.leTrans m (Succ m) highest (Nat.leSucc m) h))

theorem stepLeftAt (highest: Nat): (a: Nat) -> a <= highest -> (n: Nat) ->
    Dial.place highest (Nat.toInt (Dial.place highest (Int.subNatNat a 1)) - Nat.toInt n)
      = Dial.place highest (Int.subNatNat a (Succ n))
  | Zero,   h, n =>
    Eq.trans (Eq.cong (\x => Dial.place highest (Nat.toInt x - Nat.toInt n)) (leftZero highest))
      (Eq.trans (Eq.cong (\x => Dial.place highest x) (subIsSubNatNat highest n)) (backFrom highest n))
  | Succ m, h, n =>
    Eq.trans (Eq.cong (\x => Dial.place highest (Nat.toInt x - Nat.toInt n)) (leftOne highest m h))
      (Eq.trans (Eq.cong (\x => Dial.place highest x) (subIsSubNatNat m n))
        (Eq.cong (\x => Dial.place highest x) (Eq.sym (subNatNatSucc m n))))

-- The count after one click left to `m`, from `Succ m`.
theorem stepLeftFrom (highest: Nat): (m: Nat) -> Succ m <= highest -> (n: Nat) ->
    Bool.toNat (m == 0) + ((Succ highest - m) % Succ highest + n) / Succ highest
      = ((Succ highest - Succ m) % Succ highest + Succ n) / Succ highest
  | Zero,   h, n =>
    Eq.trans (Eq.cong (\x => Succ ((x + n) / Succ highest)) (Nat.modSelf (Succ highest)))
      (Eq.sym (Eq.trans (Eq.cong (\x => (x + Succ n) / Succ highest) (Nat.modSmall highest (Succ highest) (Nat.leRefl highest)))
        (Eq.trans (Eq.cong (\x => x / Succ highest) (Nat.addSucc highest n)) (Nat.addDivSelf (Succ highest) n))))
  | Succ j, h, n =>
    Eq.trans (Eq.cong (\x => (x + n) / Succ highest)
        (Eq.trans (Nat.modSmall (highest - j) (Succ highest) (Nat.subLe highest j))
          (Nat.subSuccRight j highest (Nat.leTrans (Succ j) (Succ (Succ j)) highest (Nat.leSucc (Succ j)) h))))
      (Eq.trans (Eq.cong (\x => x / Succ highest) (Eq.sym (Nat.addSucc (highest - Succ j) n)))
        (Eq.cong (\x => (x + Succ n) / Succ highest) (Eq.sym (Nat.modSmall (highest - Succ j) (Succ highest) (Nat.subLe highest (Succ j))))))

-- The count after one click left from 0, to `highest`.
theorem stepLeftTop: (highest: Nat) -> (n: Nat) ->
    Bool.toNat (highest == 0) + ((Succ highest - highest) % Succ highest + n) / Succ highest
      = ((Succ highest - 0) % Succ highest + Succ n) / Succ highest
  | Zero,   n => Eq.trans (Eq.cong Succ (Nat.divOne n)) (Eq.sym (Nat.divOne (Succ n)))
  | Succ t, n =>
    Eq.trans (Eq.cong (\x => (x % Succ (Succ t) + n) / Succ (Succ t)) (Nat.succSub t))
      (Eq.trans (Eq.cong (\x => (x + n) / Succ (Succ t)) (Nat.modSmall 1 (Succ (Succ t)) rfl))
        (Eq.sym (Eq.cong (\x => (x + Succ n) / Succ (Succ t)) (Nat.modSelf (Succ (Succ t))))))

theorem stepLeft (highest: Nat): (a: Nat) -> a <= highest -> (n: Nat) ->
    Bool.toNat (Dial.place highest (Int.subNatNat a 1) == 0)
        + ((Succ highest - Dial.place highest (Int.subNatNat a 1)) % Succ highest + n) / Succ highest
      = ((Succ highest - a) % Succ highest + Succ n) / Succ highest
  | Zero,   h, n =>
    Eq.trans (Eq.cong (\x => Bool.toNat (x == 0) + ((Succ highest - x) % Succ highest + n) / Succ highest) (leftZero highest))
      (stepLeftTop highest n)
  | Succ m, h, n =>
    Eq.trans (Eq.cong (\x => Bool.toNat (x == 0) + ((Succ highest - x) % Succ highest + n) / Succ highest) (leftOne highest m h))
      (stepLeftFrom highest m h n)

theorem leftAt [highest: Nat] (d: Dial highest): (n: Nat) ->
    (List.foldLeft Dial.move d (List.replicate n (Left 1))).position = Dial.place highest (Nat.toInt d.position - Nat.toInt n)
  | Zero   => Eq.sym (Eq.trans (Eq.cong (\x => x % Succ highest) (Nat.addZero d.position)) (Nat.modSmall d.position (Succ highest) d.inRange))
  | Succ n => Eq.trans (leftAt (d.move (Left 1)) n) (stepLeftAt highest d.position d.inRange n)

theorem leftCount [highest: Nat] (d: Dial highest): (n: Nat) ->
    zerosAfter d (List.replicate n (Left 1)) = ((Succ highest - d.position) % Succ highest + n) / Succ highest
  | Zero   =>
    Eq.sym (Eq.trans (Eq.cong (\x => x / Succ highest) (Nat.addZero ((Succ highest - d.position) % Succ highest)))
      (Nat.divSmall ((Succ highest - d.position) % Succ highest) (Succ highest) (Nat.modLt (Succ highest - d.position) (Succ highest))))
  | Succ n =>
    Eq.trans (Eq.cong (List.occurrences Dial.isZero) (List.scanLeftCons Dial.move (d.move (Left 1)) (List.replicate n (Left 1))))
      (Eq.trans (Eq.cong (\t => Bool.toNat (d.move (Left 1)).isZero + t) (leftCount (d.move (Left 1)) n))
        (stepLeft highest d.position d.inRange n))

-- A turn is its clicks, one at a time: it ends in the same place, and
-- `zerosDuring` counts the clicks that land on 0.
theorem turnAt (d: Dial highest): (t: Turn) -> List.foldLeft Dial.move d t.clicks = d.move t
  | Left n  => dialExt (List.foldLeft Dial.move d (Left n).clicks) (d.move (Left n)) (leftAt d n)
  | Right n => dialExt (List.foldLeft Dial.move d (Right n).clicks) (d.move (Right n)) (rightAt d n)

theorem turnCount (d: Dial highest): (t: Turn) -> zerosAfter d t.clicks = d.zerosDuring t
  | Left n  => leftCount d n
  | Right n => rightCount d n

-- The clicks of one turn, then the rest.
theorem zerosPassedSplit (d: Dial highest) (t: Turn) (ts: List Turn):
    zerosAfter d (t.clicks ++ List.concatMap Turn.clicks ts)
      = d.zerosDuring t + zerosAfter (d.move t) (List.concatMap Turn.clicks ts) :=
  Eq.trans (Eq.cong (List.occurrences Dial.isZero) (List.scanLeftAppend Dial.move d t.clicks (List.concatMap Turn.clicks ts)))
    (Eq.trans (List.occurrencesAppend Dial.isZero (List.drop 1 (List.scanLeft Dial.move d t.clicks))
        (List.drop 1 (List.scanLeft Dial.move (List.foldLeft Dial.move d t.clicks) (List.concatMap Turn.clicks ts))))
      (Eq.trans (Eq.cong (\x => x + zerosAfter (List.foldLeft Dial.move d t.clicks) (List.concatMap Turn.clicks ts))
          (turnCount d t))
        (Eq.cong (\e => d.zerosDuring t + zerosAfter e (List.concatMap Turn.clicks ts)) (turnAt d t))))

theorem zerosPassedFrom (d: Dial highest): (ts: List Turn) ->
    zerosPassed d ts = zerosAfter d (List.concatMap Turn.clicks ts)
  | Nil       => rfl
  | Cons t ts =>
    Eq.trans (List.sumCons (d.zerosDuring t) (List.zipWith Dial.zerosDuring (List.scanLeft Dial.move (d.move t) ts) ts))
      (Eq.trans (Eq.cong (\x => d.zerosDuring t + x) (zerosPassedFrom (d.move t) ts))
        (Eq.sym (zerosPassedSplit d t ts)))
