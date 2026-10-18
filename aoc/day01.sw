-- Advent of Code 2025, day 1: a dial numbered 0 to 99 starts at 50 and is
-- turned left or right. Part 1 counts the turns that end on 0; part 2 counts
-- every click that lands on 0, including those in the middle of a turn.
--
--   $ stitchwort run aoc/day01.sw < aoc/inputs/day01.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- The dial's size is a parameter, `top` being its largest number (99 in the
-- puzzle). The proofs below are about any dial; besides being more general,
-- that keeps them fast to check (see "Proofs" below).

type Turn =
  | Left (clicks : Nat)
  | Right (clicks : Nat)

-- "L68" is `Left 68`.
def parseTurn (t : Text) : Maybe Turn :=
  match Text.uncons t with
    | Nothing           => Nothing
    | Just (c, rest)    => turnOf c (Text.toNat rest)

def turnOf (c : Char) : Maybe Nat -> Maybe Turn
  | Nothing => Nothing
  | Just n  => if c == 'L' then Just (Left n) else if c == 'R' then Just (Right n) else Nothing

-- A position on a dial numbered 0 to `top`, with the proof that it's on it.
type Pos (top : Nat) = { at : Nat, ok : at <= top }

-- Where an integer lands on a dial numbered 0 to `top`.
def place (top : Nat) (x : Int) : Nat := Int.modNat x (Succ top)

-- Any integer, wrapped onto the dial.
def wrap (top : Nat) (x : Int) : Pos top := { at = place top x, ok = Int.modNatLt x (Succ top) }

-- Where a turn leaves the dial.
def move (top : Nat) (p : Pos top) : Turn -> Pos top
  | Left n  => wrap top (p.at.toInt - n.toInt)
  | Right n => wrap top (p.at.toInt + n.toInt)

def isZero [top : Nat] (p : Pos top) : Bool := p.at == 0

-- How many clicks of a turn land on 0. Going right from `p`, the dial is at
-- 0 after each click that brings `p + k` to a multiple of the dial's size.
-- Going left is the mirror image: 0 is `(size - p) % size` clicks away.
def passes (top : Nat) (p : Pos top) : Turn -> Nat
  | Right n => (p.at + n) / Succ top
  | Left n  => ((Succ top - p.at) % Succ top + n) / Succ top

-- Part 1: the positions after each turn that are 0.
def part1 (top : Nat) (start : Pos top) (turns : List Turn) : Nat := ((List.scanl (move top) start turns).drop 1).count isZero

-- Part 2: add up the passes, turn by turn.
def part2 (top : Nat) (start : Pos top) (turns : List Turn) : Nat := Pair.snd (List.foldl (step top) (start, 0) turns)

def step (top : Nat) : (Pos top, Nat) -> Turn -> (Pos top, Nat)
  | (p, count), t => (move top p t, count + passes top p t)

-- The specification of part 2: turn the dial one click at a time, and count
-- the positions after each click that are 0.
def clicks : Turn -> List Turn
  | Left n  => List.replicate n (Left 1)
  | Right n => List.replicate n (Right 1)

def part2Spec (top : Nat) (start : Pos top) (turns : List Turn) : Nat := ((List.scanl (move top) start (List.concatMap clicks turns)).drop 1).count isZero

-- The puzzle's dial.
def start : Pos 99 := wrap 99 50

def solve (lines : List Text) : (Nat, Nat) :=
  let turns := lines.mapMaybe parseTurn
  (part1 99 start turns, part2 99 start turns)

def main () : {IO} () := report (solve (IO.readAllLines ()))

def report : (Nat, Nat) -> {IO} ()
  | (a, b) =>
    print ("Part 1: " ++ Nat.toText a)
    print ("Part 2: " ++ Nat.toText b)

def example : List Text := ["L68", "L30", "R48", "L5", "R60", "L55", "L1", "L99", "R14", "L82"]

def after (t : Text) : Maybe Nat := Maybe.map (\turn => (move 99 start turn).at) (parseTurn t)

def count (x : Int) (t : Turn) : Nat := passes 99 (wrap 99 x) t

test "example" := solve example == (3, 6)
test "example, click by click" := part2Spec 99 start (example.mapMaybe parseTurn) == 6
test "parse" := after "L68" == Just 82
test "parse right" := after "R5" == Just 55
test "parse junk" := after "X5" == Nothing
test "left past zero" := count 10 (Left 40) == 1
test "left onto zero" := count 20 (Left 20) == 1
test "right onto zero" := count 0 (Right 100) == 1
test "left from zero" := count 0 (Left 42) == 0
test "left a full turn from zero" := count 0 (Left 200) == 2

theorem exampleAnswer : solve example = (3, 6) := rfl

-- Proofs ------------------------------------------------------------------
--
-- Theorem 1 (positions stay on the dial) holds by the type `Pos`, and part 1
-- is its own specification (theorem 3, `part1Puzzle`). Theorem 2,
-- `part2Correct`, says the arithmetic count `passes` agrees with turning the
-- dial one click at a time, for any dial, start and list of turns.
--
-- The lemmas are about a dial of any size, `Succ top`: with the literal 100,
-- `x % 100` unfolds to `x - 100 * (x / 100)`, and `100 * q` to a hundred
-- additions, so every comparison of such types took seconds. With a
-- variable size the multiplication stays as it is.

-- Integers.
theorem subNatNatFromSucc (m : Nat) (n : Nat) : (k : Nat) -> Int.subNatNatFrom (Succ m) (Succ n) k = Int.subNatNatFrom m n k
  | Zero   => rfl
  | Succ k => rfl

theorem subNatNatSucc (m : Nat) (n : Nat) : Int.subNatNat (Succ m) (Succ n) = Int.subNatNat m n := subNatNatFromSucc m n (n - m)

theorem subNatNatZero (m : Nat) : Int.subNatNat m 0 = Nat.toInt m := Eq.cong (\k => Int.subNatNatFrom m 0 k) (Nat.zeroSub m)

theorem subIsSubNatNat (m : Nat) : (n : Nat) -> Nat.toInt m - Nat.toInt n = Int.subNatNat m n
  | Zero   => Eq.trans (Eq.cong Nat.toInt (Nat.addZero m)) (Eq.sym (subNatNatZero m))
  | Succ n => rfl


-- Two positions at the same place are the same.
theorem posExt : [top : Nat] -> (p : Pos top) -> (q : Pos top) -> p.at = q.at -> p = q
  | { at = a, ok = h1 }, { at = b, ok = h2 }, e => posExtAt top a h1 b e h2

theorem posExtAt (top : Nat) (a : Nat) (h1 : a <= top) (b : Nat) (e : a = b) : (h2 : b <= top) ->
    ({ at = a, ok = h1 } : Pos top) = { at = b, ok = h2 } :=
  J (\y e2 => (h3 : y <= top) -> ({ at = a, ok = h1 } : Pos top) = { at = y, ok = h3 })
    (\h3 => J (\h e3 => ({ at = a, ok = h1 } : Pos top) = { at = a, ok = h }) rfl (Bool.uniqueEq (Nat.leq a top) True h1 h3))
    e

-- Theorem 1: every position is on the dial, by its type.
theorem alwaysOnDial (top : Nat) (p : Pos top) (t : Turn) : (move top p t).at <= top := (move top p t).ok

-- One click right on a dial of size `d`: from `a + 1 = d` the dial goes to
-- 0, otherwise to `a + 1`.
theorem rightCases (d : Nat) [auto ok : d != 0] (a : Nat) (h : a < d) (goal : Prop)
    (top : a + 1 = d -> goal) (below : Succ a < d -> goal) : goal :=
  Bool.inspect (Nat.leq d (Succ a)) (\b => goal)
    (\t => top (Eq.trans (Nat.addOne a) (Nat.leAntisym (Succ a) d h t)))
    (\f => below (Nat.leqFalse d (Succ a) f))

theorem stepRightAt (d : Nat) [auto ok : d != 0] (a : Nat) (h : a < d) (n : Nat) :
    ((a + 1) % d + n) % d = (a + Succ n) % d :=
  rightCases d a h (((a + 1) % d + n) % d = (a + Succ n) % d)
    (\e => Eq.trans (Eq.cong (\x => (x + n) % d) (Eq.trans (Eq.cong (\x => x % d) e) (Nat.modSelf d)))
      (Eq.sym (Eq.trans (Eq.cong (\x => x % d) (Eq.trans (Nat.addSucc a n) (Eq.cong (\x => x + n) (Eq.trans (Eq.sym (Nat.addOne a)) e))))
        (Nat.addModSelf d n))))
    (\lt => Eq.trans (Eq.cong (\x => (x + n) % d) (Eq.trans (Eq.cong (\x => x % d) (Nat.addOne a)) (Nat.modSmall (Succ a) d lt)))
      (Eq.cong (\x => x % d) (Eq.sym (Nat.addSucc a n))))

theorem stepRight (d : Nat) [auto ok : d != 0] (a : Nat) (h : a < d) (n : Nat) :
    Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d = (a + Succ n) / d :=
  rightCases d a h (Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d = (a + Succ n) / d)
    (\e => Eq.trans (Eq.cong (\x => Bool.toNat (x == 0) + (x + n) / d) (Eq.trans (Eq.cong (\x => x % d) e) (Nat.modSelf d)))
      (Eq.sym (Eq.trans (Eq.cong (\x => x / d) (Eq.trans (Nat.addSucc a n) (Eq.cong (\x => x + n) (Eq.trans (Eq.sym (Nat.addOne a)) e))))
        (Nat.addDivSelf d n))))
    (\lt => Eq.trans (Eq.cong (\x => Bool.toNat (x == 0) + (x + n) / d) (Eq.trans (Eq.cong (\x => x % d) (Nat.addOne a)) (Nat.modSmall (Succ a) d lt)))
      (Eq.cong (\x => x / d) (Eq.sym (Nat.addSucc a n))))

theorem rightAt (top : Nat) (p : Pos top) : (n : Nat) ->
    (List.foldl (move top) p (List.replicate n (Right 1))).at = (p.at + n) % Succ top
  | Zero   => Eq.sym (Eq.trans (Eq.cong (\x => x % Succ top) (Nat.addZero p.at)) (Nat.modSmall p.at (Succ top) p.ok))
  | Succ n => Eq.trans (rightAt top (move top p (Right 1)) n) (stepRightAt (Succ top) p.at p.ok n)

theorem rightCount (top : Nat) (p : Pos top) : (n : Nat) ->
    List.occurrences isZero (List.drop 1 (List.scanl (move top) p (List.replicate n (Right 1)))) = (p.at + n) / Succ top
  | Zero   => Eq.sym (Eq.trans (Eq.cong (\x => x / Succ top) (Nat.addZero p.at)) (Nat.divSmall p.at (Succ top) p.ok))
  | Succ n =>
    Eq.trans (Eq.cong (List.occurrences isZero) (List.scanlCons (move top) (move top p (Right 1)) (List.replicate n (Right 1))))
      (Eq.trans (Eq.cong (\t => Bool.toNat (isZero (move top p (Right 1))) + t) (rightCount top (move top p (Right 1)) n))
        (stepRight (Succ top) p.at p.ok n))

-- Going left from 0 on a dial of size `Succ m` ends at `m - n % Succ m`.
theorem backFrom (m : Nat) (n : Nat) : place m (Int.subNatNat m n) = m - n % Succ m :=
  Bool.inspect (Nat.leq n m) (\b => place m (Int.subNatNat m n) = m - n % Succ m)
    (\h => Eq.trans (Eq.cong (\k => place m (Int.subNatNatFrom m n k)) (Nat.subEqZero n m h))
      (Eq.trans (Nat.modSmall (m - n) (Succ m) (Nat.subLe m n)) (Eq.sym (Eq.cong (\x => m - x) (Nat.modSmall n (Succ m) h)))))
    (\f => J (\y e => place m (Int.subNatNat m y) = m - y % Succ m)
      (backFar m (n - Succ m)) (Nat.addSubCancel (Succ m) n (Nat.leqFalse n m f)))

theorem backFar (m : Nat) (r : Nat) : place m (Int.subNatNat m (Succ m + r)) = m - (Succ m + r) % Succ m :=
  Eq.trans (Eq.cong (\k => place m (Int.subNatNatFrom m (Succ m + r) k)) (Nat.succAddSub m r))
    (Eq.sym (Eq.cong (\x => m - x) (Nat.addModSelf (Succ m) r)))

-- One click left: from 0 to `top`, otherwise down by one.
theorem leftZero (top : Nat) : place top (Int.subNatNat 0 1) = top := Eq.cong (\x => top - x) (Nat.modSmall 0 (Succ top) rfl)

theorem leftOne (top : Nat) (m : Nat) (h : Succ m <= top) : place top (Int.subNatNat (Succ m) 1) = m :=
  Eq.trans (Eq.cong (\x => place top x) (Eq.trans (subNatNatSucc m 0) (subNatNatZero m)))
    (Nat.modSmall m (Succ top) (Nat.leTrans m (Succ m) top (Nat.leSucc m) h))

theorem stepLeftAt (top : Nat) : (a : Nat) -> a <= top -> (n : Nat) ->
    place top (Nat.toInt (place top (Int.subNatNat a 1)) - Nat.toInt n)
      = place top (Int.subNatNat a (Succ n))
  | Zero,   h, n =>
    Eq.trans (Eq.cong (\x => place top (Nat.toInt x - Nat.toInt n)) (leftZero top))
      (Eq.trans (Eq.cong (\x => place top x) (subIsSubNatNat top n)) (backFrom top n))
  | Succ m, h, n =>
    Eq.trans (Eq.cong (\x => place top (Nat.toInt x - Nat.toInt n)) (leftOne top m h))
      (Eq.trans (Eq.cong (\x => place top x) (subIsSubNatNat m n))
        (Eq.cong (\x => place top x) (Eq.sym (subNatNatSucc m n))))


-- The count after one click left to `m`, from `Succ m`.
theorem stepLeftFrom (top : Nat) : (m : Nat) -> Succ m <= top -> (n : Nat) ->
    Bool.toNat (m == 0) + ((Succ top - m) % Succ top + n) / Succ top = ((Succ top - Succ m) % Succ top + Succ n) / Succ top
  | Zero,   h, n =>
    Eq.trans (Eq.cong (\x => Succ ((x + n) / Succ top)) (Nat.modSelf (Succ top)))
      (Eq.sym (Eq.trans (Eq.cong (\x => (x + Succ n) / Succ top) (Nat.modSmall top (Succ top) (Nat.leRefl top)))
        (Eq.trans (Eq.cong (\x => x / Succ top) (Nat.addSucc top n)) (Nat.addDivSelf (Succ top) n))))
  | Succ j, h, n =>
    Eq.trans (Eq.cong (\x => (x + n) / Succ top)
        (Eq.trans (Nat.modSmall (top - j) (Succ top) (Nat.subLe top j)) (Nat.subSuccRight j top (Nat.leTrans (Succ j) (Succ (Succ j)) top (Nat.leSucc (Succ j)) h))))
      (Eq.trans (Eq.cong (\x => x / Succ top) (Eq.sym (Nat.addSucc (top - Succ j) n)))
        (Eq.cong (\x => (x + Succ n) / Succ top) (Eq.sym (Nat.modSmall (top - Succ j) (Succ top) (Nat.subLe top (Succ j))))))

-- The count after one click left from 0, to `top`.
theorem stepLeftTop : (top : Nat) -> (n : Nat) ->
    Bool.toNat (top == 0) + ((Succ top - top) % Succ top + n) / Succ top = ((Succ top - 0) % Succ top + Succ n) / Succ top
  | Zero,   n => Eq.trans (Eq.cong Succ (Nat.divOne n)) (Eq.sym (Nat.divOne (Succ n)))
  | Succ t, n =>
    Eq.trans (Eq.cong (\x => (x % Succ (Succ t) + n) / Succ (Succ t)) (Nat.succSub t))
      (Eq.trans (Eq.cong (\x => (x + n) / Succ (Succ t)) (Nat.modSmall 1 (Succ (Succ t)) rfl))
        (Eq.sym (Eq.cong (\x => (x + Succ n) / Succ (Succ t)) (Nat.modSelf (Succ (Succ t))))))

theorem stepLeft (top : Nat) : (a : Nat) -> a <= top -> (n : Nat) ->
    Bool.toNat (place top (Int.subNatNat a 1) == 0) + ((Succ top - place top (Int.subNatNat a 1)) % Succ top + n) / Succ top
      = ((Succ top - a) % Succ top + Succ n) / Succ top
  | Zero,   h, n =>
    Eq.trans (Eq.cong (\x => Bool.toNat (x == 0) + ((Succ top - x) % Succ top + n) / Succ top) (leftZero top)) (stepLeftTop top n)
  | Succ m, h, n =>
    Eq.trans (Eq.cong (\x => Bool.toNat (x == 0) + ((Succ top - x) % Succ top + n) / Succ top) (leftOne top m h)) (stepLeftFrom top m h n)

theorem leftAt (top : Nat) (p : Pos top) : (n : Nat) ->
    (List.foldl (move top) p (List.replicate n (Left 1))).at = place top (Nat.toInt p.at - Nat.toInt n)
  | Zero   => Eq.sym (Eq.trans (Eq.cong (\x => x % Succ top) (Nat.addZero p.at)) (Nat.modSmall p.at (Succ top) p.ok))
  | Succ n => Eq.trans (leftAt top (move top p (Left 1)) n) (stepLeftAt top p.at p.ok n)

theorem leftCount (top : Nat) (p : Pos top) : (n : Nat) ->
    List.occurrences isZero (List.drop 1 (List.scanl (move top) p (List.replicate n (Left 1)))) = ((Succ top - p.at) % Succ top + n) / Succ top
  | Zero   =>
    Eq.sym (Eq.trans (Eq.cong (\x => x / Succ top) (Nat.addZero ((Succ top - p.at) % Succ top)))
      (Nat.divSmall ((Succ top - p.at) % Succ top) (Succ top) (Nat.modLt (Succ top - p.at) (Succ top))))
  | Succ n =>
    Eq.trans (Eq.cong (List.occurrences isZero) (List.scanlCons (move top) (move top p (Left 1)) (List.replicate n (Left 1))))
      (Eq.trans (Eq.cong (\t => Bool.toNat (isZero (move top p (Left 1))) + t) (leftCount top (move top p (Left 1)) n))
        (stepLeft top p.at p.ok n))

-- A turn is its clicks, one at a time: it ends in the same place, and
-- `passes` counts the clicks that land on 0.
theorem turnAt (top : Nat) (p : Pos top) : (t : Turn) -> List.foldl (move top) p (clicks t) = move top p t
  | Left n  => posExt (List.foldl (move top) p (clicks (Left n))) (move top p (Left n)) (leftAt top p n)
  | Right n => posExt (List.foldl (move top) p (clicks (Right n))) (move top p (Right n)) (rightAt top p n)

theorem turnCount (top : Nat) (p : Pos top) : (t : Turn) ->
    List.occurrences isZero (List.drop 1 (List.scanl (move top) p (clicks t))) = passes top p t
  | Left n  => leftCount top p n
  | Right n => rightCount top p n

-- The clicks of one turn, then the rest.
theorem part2Split (top : Nat) (p : Pos top) (t : Turn) (ts : List Turn) :
    List.occurrences isZero (List.drop 1 (List.scanl (move top) p (clicks t ++ List.concatMap clicks ts)))
      = passes top p t + List.occurrences isZero (List.drop 1 (List.scanl (move top) (move top p t) (List.concatMap clicks ts))) :=
  Eq.trans (Eq.cong (List.occurrences isZero) (List.scanlAppend (move top) p (clicks t) (List.concatMap clicks ts)))
    (Eq.trans (List.occurrencesAppend isZero (List.drop 1 (List.scanl (move top) p (clicks t)))
        (List.drop 1 (List.scanl (move top) (List.foldl (move top) p (clicks t)) (List.concatMap clicks ts))))
      (Eq.trans (Eq.cong (\x => x + List.occurrences isZero (List.drop 1 (List.scanl (move top) (List.foldl (move top) p (clicks t)) (List.concatMap clicks ts))))
          (turnCount top p t))
        (Eq.cong (\q => passes top p t + List.occurrences isZero (List.drop 1 (List.scanl (move top) q (List.concatMap clicks ts))))
          (turnAt top p t))))

theorem part2From (top : Nat) (p : Pos top) (acc : Nat) : (ts : List Turn) ->
    Pair.snd (List.foldl (step top) (p, acc) ts) = acc + List.occurrences isZero (List.drop 1 (List.scanl (move top) p (List.concatMap clicks ts)))
  | Nil       => Eq.sym (Nat.addZero acc)
  | Cons t ts =>
    Eq.trans (part2From top (move top p t) (acc + passes top p t) ts)
      (Eq.trans (Nat.addAssoc acc (passes top p t) (List.occurrences isZero (List.drop 1 (List.scanl (move top) (move top p t) (List.concatMap clicks ts)))))
        (Eq.cong (\x => acc + x) (Eq.sym (part2Split top p t ts))))

-- Theorem 2: the arithmetic count is the click-by-click count, for any dial,
-- start and turns.
theorem part2Correct (top : Nat) (start : Pos top) (turns : List Turn) : part2 top start turns = part2Spec top start turns :=
  Eq.trans (part2From top start 0 turns)
    (Eq.sym (List.countOccurrences isZero (List.drop 1 (List.scanl (move top) start (List.concatMap clicks turns)))))

-- And so for the puzzle's answer.
theorem part2Puzzle (lines : List Text) : Pair.snd (solve lines) = part2Spec 99 start (lines.mapMaybe parseTurn) := part2Correct 99 start (lines.mapMaybe parseTurn)

-- Theorem 3: part 1 is the count of the positions after each turn that are 0.
theorem part1Puzzle (lines : List Text) :
    Pair.fst (solve lines) = ((List.scanl (move 99) start (lines.mapMaybe parseTurn)).drop 1).count isZero := rfl
