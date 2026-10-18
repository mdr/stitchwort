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
parseTurn : Text -> Maybe Turn
parseTurn t =
  match Text.uncons t with
    | Nothing           -> Nothing
    | Just (c, rest)    -> turnOf c (Text.toNat rest)

turnOf : Char -> Maybe Nat -> Maybe Turn
turnOf c Nothing  = Nothing
turnOf c (Just n) = if c == 'L' then Just (Left n) else if c == 'R' then Just (Right n) else Nothing

-- A position on a dial numbered 0 to `top`, with the proof that it's on it.
type Pos (top : Nat) = { at : Nat, ok : at <= top }

-- Where an integer lands on a dial numbered 0 to `top`.
place : (top : Nat) -> Int -> Nat
place top x = Int.modNat x (Succ top)

-- Any integer, wrapped onto the dial.
wrap : (top : Nat) -> Int -> Pos top
wrap top x = { at = place top x, ok = quickLt (place top x) (Succ top) (\u -> Int.modNatLt x (Succ top)) }

-- `stitchwort run` erases proofs, but checking still computes one where a type
-- mentions a concrete position (with `ok = Int.modNatLt x (Succ top)` this
-- file takes about 16 s to check), and `Int.modNatLt` takes thousands of
-- steps. Comparing the numbers is one step, and gives the same proposition;
-- the slow proof only rules out the other answer, so it never runs.
theorem quickLt : (n : Nat) -> (d : Nat) -> (() -> n < d) -> n < d
quickLt n d slow =
  Bool.inspect (Nat.leq (Succ n) d) (\b -> b = True) (\h -> rfl)
    (\h -> Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym h) (slow ()))))

-- Where a turn leaves the dial.
move : (top : Nat) -> Pos top -> Turn -> Pos top
move top p (Left n)  = wrap top (p.at.toInt - n.toInt)
move top p (Right n) = wrap top (p.at.toInt + n.toInt)

isZero : [top : Nat] -> Pos top -> Bool
isZero p = p.at == 0

-- How many clicks of a turn land on 0. Going right from `p`, the dial is at
-- 0 after each click that brings `p + k` to a multiple of the dial's size.
-- Going left is the mirror image: 0 is `(size - p) % size` clicks away.
passes : (top : Nat) -> Pos top -> Turn -> Nat
passes top p (Right n) = (p.at + n) / Succ top
passes top p (Left n)  = ((Succ top - p.at) % Succ top + n) / Succ top

-- Part 1: the positions after each turn that are 0.
part1 : (top : Nat) -> Pos top -> List Turn -> Nat
part1 top start turns = ((List.scanl (move top) start turns).drop 1).count isZero

-- Part 2: add up the passes, turn by turn.
part2 : (top : Nat) -> Pos top -> List Turn -> Nat
part2 top start turns = Pair.snd (List.foldl (step top) (start, 0) turns)

step : (top : Nat) -> (Pos top, Nat) -> Turn -> (Pos top, Nat)
step top (p, count) t = (move top p t, count + passes top p t)

-- The specification of part 2: turn the dial one click at a time, and count
-- the positions after each click that are 0.
clicks : Turn -> List Turn
clicks (Left n)  = List.replicate n (Left 1)
clicks (Right n) = List.replicate n (Right 1)

part2Spec : (top : Nat) -> Pos top -> List Turn -> Nat
part2Spec top start turns = ((List.scanl (move top) start (List.concatMap clicks turns)).drop 1).count isZero

-- The puzzle's dial.
start : Pos 99
start = wrap 99 50

solve : List Text -> (Nat, Nat)
solve lines =
  let turns = lines.mapMaybe parseTurn
  (part1 99 start turns, part2 99 start turns)

main : () -> {IO, Partial} ()
main u = report (solve (IO.readAllLines ()))

report : (Nat, Nat) -> {IO} ()
report (a, b) =
  print ("Part 1: " ++ Nat.toText a)
  print ("Part 2: " ++ Nat.toText b)

example : List Text
example = ["L68", "L30", "R48", "L5", "R60", "L55", "L1", "L99", "R14", "L82"]

after : Text -> Maybe Nat
after t = Maybe.map (\turn -> (move 99 start turn).at) (parseTurn t)

count : Int -> Turn -> Nat
count x t = passes 99 (wrap 99 x) t

test "example" = solve example == (3, 6)
test "example, click by click" = part2Spec 99 start (example.mapMaybe parseTurn) == 6
test "parse" = after "L68" == Just 82
test "parse right" = after "R5" == Just 55
test "parse junk" = after "X5" == Nothing
test "left past zero" = count 10 (Left 40) == 1
test "left onto zero" = count 20 (Left 20) == 1
test "right onto zero" = count 0 (Right 100) == 1
test "left from zero" = count 0 (Left 42) == 0
test "left a full turn from zero" = count 0 (Left 200) == 2

theorem exampleAnswer : solve example = (3, 6)
exampleAnswer = rfl

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
theorem subNatNatFromSucc : (m : Nat) -> (n : Nat) -> (k : Nat) -> Int.subNatNatFrom (Succ m) (Succ n) k = Int.subNatNatFrom m n k
subNatNatFromSucc m n Zero     = rfl
subNatNatFromSucc m n (Succ k) = rfl

theorem subNatNatSucc : (m : Nat) -> (n : Nat) -> Int.subNatNat (Succ m) (Succ n) = Int.subNatNat m n
subNatNatSucc m n = subNatNatFromSucc m n (n - m)

theorem subNatNatZero : (m : Nat) -> Int.subNatNat m 0 = Nat.toInt m
subNatNatZero m = Eq.cong (\k -> Int.subNatNatFrom m 0 k) (Nat.zeroSub m)

theorem subIsSubNatNat : (m : Nat) -> (n : Nat) -> Nat.toInt m - Nat.toInt n = Int.subNatNat m n
subIsSubNatNat m Zero     = Eq.trans (Eq.cong Nat.toInt (Nat.addZero m)) (Eq.sym (subNatNatZero m))
subIsSubNatNat m (Succ n) = rfl


-- Two positions at the same place are the same.
theorem posExt : [top : Nat] -> (p : Pos top) -> (q : Pos top) -> p.at = q.at -> p = q
posExt { at = a, ok = h1 } { at = b, ok = h2 } e = posExtAt top a h1 b e h2

theorem posExtAt : (top : Nat) -> (a : Nat) -> (h1 : a <= top) -> (b : Nat) -> a = b -> (h2 : b <= top) ->
    ({ at = a, ok = h1 } : Pos top) = { at = b, ok = h2 }
posExtAt top a h1 b e =
  J (\y e2 -> (h3 : y <= top) -> ({ at = a, ok = h1 } : Pos top) = { at = y, ok = h3 })
    (\h3 -> J (\h e3 -> ({ at = a, ok = h1 } : Pos top) = { at = a, ok = h }) rfl (Bool.uniqueEq (Nat.leq a top) True h1 h3))
    e

-- Theorem 1: every position is on the dial, by its type.
theorem alwaysOnDial : (top : Nat) -> (p : Pos top) -> (t : Turn) -> (move top p t).at <= top
alwaysOnDial top p t = (move top p t).ok

-- One click right on a dial of size `d`: from `a + 1 = d` the dial goes to
-- 0, otherwise to `a + 1`.
theorem rightCases : (d : Nat) -> [auto ok : d != 0] -> (a : Nat) -> a < d -> (goal : Prop) ->
    (a + 1 = d -> goal) -> (Succ a < d -> goal) -> goal
rightCases d a h goal top below =
  Bool.inspect (Nat.leq d (Succ a)) (\b -> goal)
    (\t -> top (Eq.trans (Nat.addOne a) (Nat.leAntisym (Succ a) d h t)))
    (\f -> below (Nat.leqFalse d (Succ a) f))

theorem stepRightAt : (d : Nat) -> [auto ok : d != 0] -> (a : Nat) -> a < d -> (n : Nat) ->
    ((a + 1) % d + n) % d = (a + Succ n) % d
stepRightAt d a h n =
  rightCases d a h (((a + 1) % d + n) % d = (a + Succ n) % d)
    (\e -> Eq.trans (Eq.cong (\x -> (x + n) % d) (Eq.trans (Eq.cong (\x -> x % d) e) (Nat.modSelf d)))
      (Eq.sym (Eq.trans (Eq.cong (\x -> x % d) (Eq.trans (Nat.addSucc a n) (Eq.cong (\x -> x + n) (Eq.trans (Eq.sym (Nat.addOne a)) e))))
        (Nat.addModSelf d n))))
    (\lt -> Eq.trans (Eq.cong (\x -> (x + n) % d) (Eq.trans (Eq.cong (\x -> x % d) (Nat.addOne a)) (Nat.modSmall (Succ a) d lt)))
      (Eq.cong (\x -> x % d) (Eq.sym (Nat.addSucc a n))))

theorem stepRight : (d : Nat) -> [auto ok : d != 0] -> (a : Nat) -> a < d -> (n : Nat) ->
    Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d = (a + Succ n) / d
stepRight d a h n =
  rightCases d a h (Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d = (a + Succ n) / d)
    (\e -> Eq.trans (Eq.cong (\x -> Bool.toNat (x == 0) + (x + n) / d) (Eq.trans (Eq.cong (\x -> x % d) e) (Nat.modSelf d)))
      (Eq.sym (Eq.trans (Eq.cong (\x -> x / d) (Eq.trans (Nat.addSucc a n) (Eq.cong (\x -> x + n) (Eq.trans (Eq.sym (Nat.addOne a)) e))))
        (Nat.addDivSelf d n))))
    (\lt -> Eq.trans (Eq.cong (\x -> Bool.toNat (x == 0) + (x + n) / d) (Eq.trans (Eq.cong (\x -> x % d) (Nat.addOne a)) (Nat.modSmall (Succ a) d lt)))
      (Eq.cong (\x -> x / d) (Eq.sym (Nat.addSucc a n))))

theorem rightAt : (top : Nat) -> (p : Pos top) -> (n : Nat) ->
    (List.foldl (move top) p (List.replicate n (Right 1))).at = (p.at + n) % Succ top
rightAt top p Zero     = Eq.sym (Eq.trans (Eq.cong (\x -> x % Succ top) (Nat.addZero p.at)) (Nat.modSmall p.at (Succ top) p.ok))
rightAt top p (Succ n) = Eq.trans (rightAt top (move top p (Right 1)) n) (stepRightAt (Succ top) p.at p.ok n)

theorem rightCount : (top : Nat) -> (p : Pos top) -> (n : Nat) ->
    List.occurrences isZero (List.drop 1 (List.scanl (move top) p (List.replicate n (Right 1)))) = (p.at + n) / Succ top
rightCount top p Zero     = Eq.sym (Eq.trans (Eq.cong (\x -> x / Succ top) (Nat.addZero p.at)) (Nat.divSmall p.at (Succ top) p.ok))
rightCount top p (Succ n) =
  Eq.trans (Eq.cong (List.occurrences isZero) (List.scanlCons (move top) (move top p (Right 1)) (List.replicate n (Right 1))))
    (Eq.trans (Eq.cong (\t -> Bool.toNat (isZero (move top p (Right 1))) + t) (rightCount top (move top p (Right 1)) n))
      (stepRight (Succ top) p.at p.ok n))

-- Going left from 0 on a dial of size `Succ m` ends at `m - n % Succ m`.
theorem backFrom : (m : Nat) -> (n : Nat) -> place m (Int.subNatNat m n) = m - n % Succ m
backFrom m n =
  Bool.inspect (Nat.leq n m) (\b -> place m (Int.subNatNat m n) = m - n % Succ m)
    (\h -> Eq.trans (Eq.cong (\k -> place m (Int.subNatNatFrom m n k)) (Nat.subEqZero n m h))
      (Eq.trans (Nat.modSmall (m - n) (Succ m) (Nat.subLe m n)) (Eq.sym (Eq.cong (\x -> m - x) (Nat.modSmall n (Succ m) h)))))
    (\f -> J (\y e -> place m (Int.subNatNat m y) = m - y % Succ m)
      (backFar m (n - Succ m)) (Nat.addSubCancel (Succ m) n (Nat.leqFalse n m f)))

theorem backFar : (m : Nat) -> (r : Nat) -> place m (Int.subNatNat m (Succ m + r)) = m - (Succ m + r) % Succ m
backFar m r =
  Eq.trans (Eq.cong (\k -> place m (Int.subNatNatFrom m (Succ m + r) k)) (Nat.succAddSub m r))
    (Eq.sym (Eq.cong (\x -> m - x) (Nat.addModSelf (Succ m) r)))

-- One click left: from 0 to `top`, otherwise down by one.
theorem leftZero : (top : Nat) -> place top (Int.subNatNat 0 1) = top
leftZero top = Eq.cong (\x -> top - x) (Nat.modSmall 0 (Succ top) rfl)

theorem leftOne : (top : Nat) -> (m : Nat) -> Succ m <= top -> place top (Int.subNatNat (Succ m) 1) = m
leftOne top m h =
  Eq.trans (Eq.cong (\x -> place top x) (Eq.trans (subNatNatSucc m 0) (subNatNatZero m)))
    (Nat.modSmall m (Succ top) (Nat.leTrans m (Succ m) top (Nat.leSucc m) h))

theorem stepLeftAt : (top : Nat) -> (a : Nat) -> a <= top -> (n : Nat) ->
    place top (Nat.toInt (place top (Int.subNatNat a 1)) - Nat.toInt n)
      = place top (Int.subNatNat a (Succ n))
stepLeftAt top Zero     h n =
  Eq.trans (Eq.cong (\x -> place top (Nat.toInt x - Nat.toInt n)) (leftZero top))
    (Eq.trans (Eq.cong (\x -> place top x) (subIsSubNatNat top n)) (backFrom top n))
stepLeftAt top (Succ m) h n =
  Eq.trans (Eq.cong (\x -> place top (Nat.toInt x - Nat.toInt n)) (leftOne top m h))
    (Eq.trans (Eq.cong (\x -> place top x) (subIsSubNatNat m n))
      (Eq.cong (\x -> place top x) (Eq.sym (subNatNatSucc m n))))


-- The count after one click left to `m`, from `Succ m`.
theorem stepLeftFrom : (top : Nat) -> (m : Nat) -> Succ m <= top -> (n : Nat) ->
    Bool.toNat (m == 0) + ((Succ top - m) % Succ top + n) / Succ top = ((Succ top - Succ m) % Succ top + Succ n) / Succ top
stepLeftFrom top Zero     h n =
  Eq.trans (Eq.cong (\x -> Succ ((x + n) / Succ top)) (Nat.modSelf (Succ top)))
    (Eq.sym (Eq.trans (Eq.cong (\x -> (x + Succ n) / Succ top) (Nat.modSmall top (Succ top) (Nat.leRefl top)))
      (Eq.trans (Eq.cong (\x -> x / Succ top) (Nat.addSucc top n)) (Nat.addDivSelf (Succ top) n))))
stepLeftFrom top (Succ j) h n =
  Eq.trans (Eq.cong (\x -> (x + n) / Succ top)
      (Eq.trans (Nat.modSmall (top - j) (Succ top) (Nat.subLe top j)) (Nat.subSuccRight j top (Nat.leTrans (Succ j) (Succ (Succ j)) top (Nat.leSucc (Succ j)) h))))
    (Eq.trans (Eq.cong (\x -> x / Succ top) (Eq.sym (Nat.addSucc (top - Succ j) n)))
      (Eq.cong (\x -> (x + Succ n) / Succ top) (Eq.sym (Nat.modSmall (top - Succ j) (Succ top) (Nat.subLe top (Succ j))))))

-- The count after one click left from 0, to `top`.
theorem stepLeftTop : (top : Nat) -> (n : Nat) ->
    Bool.toNat (top == 0) + ((Succ top - top) % Succ top + n) / Succ top = ((Succ top - 0) % Succ top + Succ n) / Succ top
stepLeftTop Zero     n = Eq.trans (Eq.cong Succ (Nat.divOne n)) (Eq.sym (Nat.divOne (Succ n)))
stepLeftTop (Succ t) n =
  Eq.trans (Eq.cong (\x -> (x % Succ (Succ t) + n) / Succ (Succ t)) (Nat.succSub t))
    (Eq.trans (Eq.cong (\x -> (x + n) / Succ (Succ t)) (Nat.modSmall 1 (Succ (Succ t)) rfl))
      (Eq.sym (Eq.cong (\x -> (x + Succ n) / Succ (Succ t)) (Nat.modSelf (Succ (Succ t))))))

theorem stepLeft : (top : Nat) -> (a : Nat) -> a <= top -> (n : Nat) ->
    Bool.toNat (place top (Int.subNatNat a 1) == 0) + ((Succ top - place top (Int.subNatNat a 1)) % Succ top + n) / Succ top
      = ((Succ top - a) % Succ top + Succ n) / Succ top
stepLeft top Zero     h n =
  Eq.trans (Eq.cong (\x -> Bool.toNat (x == 0) + ((Succ top - x) % Succ top + n) / Succ top) (leftZero top)) (stepLeftTop top n)
stepLeft top (Succ m) h n =
  Eq.trans (Eq.cong (\x -> Bool.toNat (x == 0) + ((Succ top - x) % Succ top + n) / Succ top) (leftOne top m h)) (stepLeftFrom top m h n)

theorem leftAt : (top : Nat) -> (p : Pos top) -> (n : Nat) ->
    (List.foldl (move top) p (List.replicate n (Left 1))).at = place top (Nat.toInt p.at - Nat.toInt n)
leftAt top p Zero     = Eq.sym (Eq.trans (Eq.cong (\x -> x % Succ top) (Nat.addZero p.at)) (Nat.modSmall p.at (Succ top) p.ok))
leftAt top p (Succ n) = Eq.trans (leftAt top (move top p (Left 1)) n) (stepLeftAt top p.at p.ok n)

theorem leftCount : (top : Nat) -> (p : Pos top) -> (n : Nat) ->
    List.occurrences isZero (List.drop 1 (List.scanl (move top) p (List.replicate n (Left 1)))) = ((Succ top - p.at) % Succ top + n) / Succ top
leftCount top p Zero     =
  Eq.sym (Eq.trans (Eq.cong (\x -> x / Succ top) (Nat.addZero ((Succ top - p.at) % Succ top)))
    (Nat.divSmall ((Succ top - p.at) % Succ top) (Succ top) (Nat.modLt (Succ top - p.at) (Succ top))))
leftCount top p (Succ n) =
  Eq.trans (Eq.cong (List.occurrences isZero) (List.scanlCons (move top) (move top p (Left 1)) (List.replicate n (Left 1))))
    (Eq.trans (Eq.cong (\t -> Bool.toNat (isZero (move top p (Left 1))) + t) (leftCount top (move top p (Left 1)) n))
      (stepLeft top p.at p.ok n))

-- A turn is its clicks, one at a time: it ends in the same place, and
-- `passes` counts the clicks that land on 0.
theorem turnAt : (top : Nat) -> (p : Pos top) -> (t : Turn) -> List.foldl (move top) p (clicks t) = move top p t
turnAt top p (Left n)  = posExt (List.foldl (move top) p (clicks (Left n))) (move top p (Left n)) (leftAt top p n)
turnAt top p (Right n) = posExt (List.foldl (move top) p (clicks (Right n))) (move top p (Right n)) (rightAt top p n)

theorem turnCount : (top : Nat) -> (p : Pos top) -> (t : Turn) ->
    List.occurrences isZero (List.drop 1 (List.scanl (move top) p (clicks t))) = passes top p t
turnCount top p (Left n)  = leftCount top p n
turnCount top p (Right n) = rightCount top p n

-- The clicks of one turn, then the rest.
theorem part2Split : (top : Nat) -> (p : Pos top) -> (t : Turn) -> (ts : List Turn) ->
    List.occurrences isZero (List.drop 1 (List.scanl (move top) p (clicks t ++ List.concatMap clicks ts)))
      = passes top p t + List.occurrences isZero (List.drop 1 (List.scanl (move top) (move top p t) (List.concatMap clicks ts)))
part2Split top p t ts =
  Eq.trans (Eq.cong (List.occurrences isZero) (List.scanlAppend (move top) p (clicks t) (List.concatMap clicks ts)))
    (Eq.trans (List.occurrencesAppend isZero (List.drop 1 (List.scanl (move top) p (clicks t)))
        (List.drop 1 (List.scanl (move top) (List.foldl (move top) p (clicks t)) (List.concatMap clicks ts))))
      (Eq.trans (Eq.cong (\x -> x + List.occurrences isZero (List.drop 1 (List.scanl (move top) (List.foldl (move top) p (clicks t)) (List.concatMap clicks ts))))
          (turnCount top p t))
        (Eq.cong (\q -> passes top p t + List.occurrences isZero (List.drop 1 (List.scanl (move top) q (List.concatMap clicks ts))))
          (turnAt top p t))))

theorem part2From : (top : Nat) -> (p : Pos top) -> (acc : Nat) -> (ts : List Turn) ->
    Pair.snd (List.foldl (step top) (p, acc) ts) = acc + List.occurrences isZero (List.drop 1 (List.scanl (move top) p (List.concatMap clicks ts)))
part2From top p acc Nil         = Eq.sym (Nat.addZero acc)
part2From top p acc (Cons t ts) =
  Eq.trans (part2From top (move top p t) (acc + passes top p t) ts)
    (Eq.trans (Nat.addAssoc acc (passes top p t) (List.occurrences isZero (List.drop 1 (List.scanl (move top) (move top p t) (List.concatMap clicks ts)))))
      (Eq.cong (\x -> acc + x) (Eq.sym (part2Split top p t ts))))

-- Theorem 2: the arithmetic count is the click-by-click count, for any dial,
-- start and turns.
theorem part2Correct : (top : Nat) -> (start : Pos top) -> (turns : List Turn) -> part2 top start turns = part2Spec top start turns
part2Correct top start turns =
  Eq.trans (part2From top start 0 turns)
    (Eq.sym (List.countOccurrences isZero (List.drop 1 (List.scanl (move top) start (List.concatMap clicks turns)))))

-- And so for the puzzle's answer.
theorem part2Puzzle : (lines : List Text) -> Pair.snd (solve lines) = part2Spec 99 start (lines.mapMaybe parseTurn)
part2Puzzle lines = part2Correct 99 start (lines.mapMaybe parseTurn)

-- Theorem 3: part 1 is the count of the positions after each turn that are 0.
theorem part1Puzzle : (lines : List Text) ->
    Pair.fst (solve lines) = ((List.scanl (move 99) start (lines.mapMaybe parseTurn)).drop 1).count isZero
part1Puzzle lines = rfl
