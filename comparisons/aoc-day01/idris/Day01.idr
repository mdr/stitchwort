||| Advent of Code 2025, day 1, in Idris 2 (base + contrib), mirroring
||| Stitchwort's aoc/src/day01/day01.sw: a dial numbered 0 to `highest` is turned left
||| or right. Part 1 counts the turns that end on 0; part 2 counts every click
||| that lands on 0. The theorem `zerosPassedCorrect` says part 2's arithmetic
||| count equals turning the dial one click at a time, for any dial, start
||| and turns.
|||
||| One deliberate difference: `move` uses only `Nat`. Idris's `Integer` is a
||| primitive type, so nothing can be proved about `x - n` for a variable `x`,
||| and the libraries have no proof-friendly integer type. Going left one
||| click is the same as going right `highest` clicks, so `Left n` adds
||| `highest * n`.
module Day01

import Data.Nat
import DialArith
import Data.List
import Data.String
import Syntax.PreorderReasoning

%default total

-- Definitions ---------------------------------------------------------------

public export
data Turn = Left Nat | Right Nat

-- "L68" is `Left 68`.
parseTurn : String -> Maybe Turn
parseTurn t = case strM t of
  StrCons 'L' rest => map Left (parsePositive rest)
  StrCons 'R' rest => map Right (parsePositive rest)
  _ => Nothing

-- A turn, one click at a time: `Left 3` is three `Left 1`s.
clicks : Turn -> List Turn
clicks (Left n)  = replicate n (Left 1)
clicks (Right n) = replicate n (Right 1)

-- All the turns, one click at a time.
allClicks : List Turn -> List Turn
allClicks [] = []
allClicks (t :: ts) = clicks t ++ allClicks ts

-- A dial numbered 0 to `highest`, at `position`.
record Dial (highest : Nat) where
  constructor MkDial
  position : Nat
  inRange : LTE position highest

-- (`modS h x` and `divS h x` divide by `S h`; see DialArith.idr.)

-- Any natural number, wrapped onto the dial.
fromNat : (h : Nat) -> Nat -> Dial h
fromNat h x = MkDial (modS h x) (fromLteSucc (modBound h x))

-- Where a turn leaves the dial.
move : {h : Nat} -> Dial h -> Turn -> Dial h
move d (Left n)  = fromNat h (position d + h * n)
move d (Right n) = fromNat h (position d + n)

isZero : Dial h -> Bool
isZero d = position d == 0

-- How many clicks of a turn land on 0.
zerosDuring : {h : Nat} -> Dial h -> Turn -> Nat
zerosDuring d (Right n) = divS h (position d + n)
zerosDuring d (Left n)  = divS h (modS h (S h `minus` position d) + n)

-- (Base has no `scanl`.)
scanl : (b -> a -> b) -> b -> List a -> List b
scanl f e [] = [e]
scanl f e (x :: xs) = e :: scanl f (f e x) xs

sumList : List Nat -> Nat
sumList [] = 0
sumList (x :: xs) = x + sumList xs

-- Part 1: the positions after each turn that are 0.
zerosLandedOn : {h : Nat} -> Dial h -> List Turn -> Nat
zerosLandedOn start turns = length (filter isZero (drop 1 (scanl move start turns)))

-- Part 2: for each turn, the clicks onto 0 from where the dial was before it.
zerosPassed : {h : Nat} -> Dial h -> List Turn -> Nat
zerosPassed start turns = sumList (zipWith zerosDuring (scanl move start turns) turns)

-- The specification of part 2: count the zeros click by click.
zerosPassedSpec : {h : Nat} -> Dial h -> List Turn -> Nat
zerosPassedSpec start turns = zerosLandedOn start (allClicks turns)

dial : Dial 99
dial = MkDial 50 (lteReflectsLTE 50 99 Refl)

solvePart1 : List Turn -> Nat
solvePart1 = zerosLandedOn dial

solvePart2 : List Turn -> Nat
solvePart2 = zerosPassed dial

example : List Turn
example = [Left 68, Left 30, Right 48, Left 5, Right 60, Left 55, Left 1, Left 99, Right 14, Left 82]

main : IO ()
main = do
  let turns = mapMaybe parseTurn ["L68", "L30", "R48", "L5", "R60", "L55", "L1", "L99", "R14", "L82"]
  printLn (solvePart1 turns, solvePart2 turns, zerosPassedSpec dial turns)

-- Proofs --------------------------------------------------------------------

-- `LTE` proofs are unique, so two dials at the same position are the same.
lteUnique : (p, q : LTE a b) -> p = q
lteUnique LTEZero LTEZero = Refl
lteUnique (LTESucc p) (LTESucc q) = cong LTESucc (lteUnique p q)

dialExt : (d, e : Dial h) -> position d = position e -> d = e
dialExt (MkDial a p) (MkDial b q) e = case e of Refl => cong (MkDial a) (lteUnique p q)

-- Division facts, each from the uniqueness of quotient and remainder.
modSmall : {h, x : Nat} -> LT x (S h) -> modS h x = x
modSmall lt = modUniq h x 0 x lt Refl

divSmall : {h, x : Nat} -> LT x (S h) -> divS h x = 0
divSmall lt = divUniq h x 0 x lt Refl

modPlus : (h, a, b : Nat) -> modS h (modS h a + b) = modS h (a + b)
modPlus h a b =
  sym (modUniq h (a + b) (divS h (modS h a + b) + divS h a) (modS h (modS h a + b))
         (modBound h (modS h a + b)) (Calc $
    |~ a + b
    ~~ (divS h a * S h + modS h a) + b
         ...(cong (+ b) (divThm h a))
    ~~ divS h a * S h + (modS h a + b)
         ...(sym (plusAssociative (divS h a * S h) (modS h a) b))
    ~~ divS h a * S h + (divS h (modS h a + b) * S h + modS h (modS h a + b))
         ...(cong (divS h a * S h +) (divThm h (modS h a + b)))
    ~~ (divS h a * S h + divS h (modS h a + b) * S h) + modS h (modS h a + b)
         ...(plusAssociative _ _ _)
    ~~ (divS h (modS h a + b) * S h + divS h a * S h) + modS h (modS h a + b)
         ...(cong (+ modS h (modS h a + b)) (plusCommutative _ _))
    ~~ (divS h (modS h a + b) + divS h a) * S h + modS h (modS h a + b)
         ...(cong (+ modS h (modS h a + b)) (sym (multDistributesOverPlusLeft _ _ _)))))

-- Adding the dial's size: one more turn of the dial.
addSelfEq : (h, n : Nat) -> S h + n = S (divS h n) * S h + modS h n
addSelfEq h n = trans (cong (S h +) (divThm h n)) (plusAssociative (S h) (divS h n * S h) (modS h n))

modAddSelf : (h, n : Nat) -> modS h (S h + n) = modS h n
modAddSelf h n = modUniq h (S h + n) (S (divS h n)) (modS h n) (modBound h n) (addSelfEq h n)

divAddSelf : (h, n : Nat) -> divS h (S h + n) = S (divS h n)
divAddSelf h n = divUniq h (S h + n) (S (divS h n)) (modS h n) (modBound h n) (addSelfEq h n)

modSelf : (h : Nat) -> modS h (S h) = 0
modSelf h = modUniq h (S h) 1 0 (LTESucc LTEZero) (sym (trans (plusZeroRightNeutral _) (plusZeroRightNeutral _)))

divOne : (n : Nat) -> divS 0 n = n
divOne n = divUniq 0 n n 0 (LTESucc LTEZero) (sym (trans (plusZeroRightNeutral _) (multOneRightNeutral n)))

-- Small facts about Nat.
lteSplit : {a, b : Nat} -> LTE a b -> Either (LT a b) (a = b)
lteSplit {b = Z} LTEZero = Right Refl
lteSplit {b = S k} LTEZero = Left (LTESucc LTEZero)
lteSplit (LTESucc p) = case lteSplit p of
  Left lt => Left (LTESucc lt)
  Right e => Right (cong S e)

minusLte : (h, j : Nat) -> LTE (minus h j) h
minusLte Z j = LTEZero
minusLte (S k) Z = reflexive
minusLte (S k) (S j) = lteSuccRight (minusLte k j)

minusSucc : (h, j : Nat) -> LTE (S j) h -> minus h j = S (minus h (S j))
minusSucc (S k) Z (LTESucc _) = cong S (sym (minusZeroRight k))
minusSucc (S k) (S j) (LTESucc p) = minusSucc k j p

-- Positions after one click.
leftZero : (h : Nat) -> modS h (0 + h * 1) = h
leftZero h = rewrite multOneRightNeutral h in modSmall (LTESucc reflexive)

leftSucc : (h, m : Nat) -> LTE (S m) h -> modS h (S m + h * 1) = m
leftSucc h m lt = Calc $
  |~ modS h (S m + h * 1)
  ~~ modS h (S h + m)  ...(cong (modS h) (trans (cong (S m +) (multOneRightNeutral h))
                            (cong S (plusCommutative m h))))
  ~~ modS h m          ...(modAddSelf h m)
  ~~ m                 ...(modSmall (LTESucc (lteSuccLeft lt)))

rightAt : {h : Nat} -> (d : Dial h) -> (n : Nat) ->
  position (foldl Day01.move d (replicate n (Right 1))) = modS h (position d + n)
rightAt d Z = rewrite plusZeroRightNeutral (position d) in sym (modSmall (LTESucc (inRange d)))
rightAt d (S n) = Calc $
  |~ position (foldl Day01.move (move d (Right 1)) (replicate n (Right 1)))
  ~~ modS h (modS h (position d + 1) + n) ...(rightAt (move d (Right 1)) n)
  ~~ modS h (position d + 1 + n)         ...(modPlus h _ n)
  ~~ modS h (position d + S n)           ...(cong (modS h) (sym (plusAssociative _ 1 n)))

leftAt : {h : Nat} -> (d : Dial h) -> (n : Nat) ->
  position (foldl Day01.move d (replicate n (Left 1))) = modS h (position d + h * n)
leftAt d Z = rewrite multZeroRightZero h in rewrite plusZeroRightNeutral (position d) in
  sym (modSmall (LTESucc (inRange d)))
leftAt d (S n) = Calc $
  |~ position (foldl Day01.move (move d (Left 1)) (replicate n (Left 1)))
  ~~ modS h (modS h (position d + h * 1) + h * n) ...(leftAt (move d (Left 1)) n)
  ~~ modS h (position d + h * 1 + h * n)         ...(modPlus h _ _)
  ~~ modS h (position d + h * S n)               ...(cong (modS h) eq)
  where
    eq : position d + h * 1 + h * n = position d + h * S n
    eq = rewrite multOneRightNeutral h in rewrite multRightSuccPlus h n in
         sym (plusAssociative _ _ _)

-- `zerosAfter d ts`: the zeros after each of `ts`, from `d`.
zerosAfter : {h : Nat} -> Dial h -> List Turn -> Nat
zerosAfter d ts = length (filter isZero (drop 1 (scanl move d ts)))

b2n : Bool -> Nat
b2n b = if b then 1 else 0

zerosAfterCons : {h : Nat} -> (d : Dial h) -> (t : Turn) -> (ts : List Turn) ->
  zerosAfter d (t :: ts) = b2n (isZero (move d t)) + zerosAfter (move d t) ts
zerosAfterCons d t [] with (isZero (move d t))
  _ | True = Refl
  _ | False = Refl
zerosAfterCons d t (u :: us) with (isZero (move d t))
  _ | True = Refl
  _ | False = Refl

zerosAfterAppend : {h : Nat} -> (d : Dial h) -> (l1, l2 : List Turn) ->
  zerosAfter d (l1 ++ l2) = zerosAfter d l1 + zerosAfter (foldl Day01.move d l1) l2
zerosAfterAppend d [] l2 = Refl
zerosAfterAppend d (t :: l1) l2 = Calc $
  |~ zerosAfter d (t :: (l1 ++ l2))
  ~~ b + zerosAfter (move d t) (l1 ++ l2)           ...(zerosAfterCons d t (l1 ++ l2))
  ~~ b + (zerosAfter (move d t) l1 + zerosAfter e l2) ...(cong (b +) (zerosAfterAppend (move d t) l1 l2))
  ~~ (b + zerosAfter (move d t) l1) + zerosAfter e l2 ...(plusAssociative _ _ _)
  ~~ zerosAfter d (t :: l1) + zerosAfter e l2       ...(cong (+ zerosAfter e l2) (sym (zerosAfterCons d t l1)))
  where
    b : Nat
    b = b2n (isZero (move d t))
    e : Dial h
    e = foldl Day01.move (move d t) l1

-- Arithmetic for one click.
stepRight : (h, a, n : Nat) -> LTE a h ->
  b2n (modS h (a + 1) == 0) + divS h (modS h (a + 1) + n) = divS h (a + S n)
stepRight h a n le = rewrite plusCommutative a 1 in case lteSplit le of
  Left lt => rewrite modSmall {h} (LTESucc lt) in cong (divS h) (plusSuccRightSucc a n)
  Right Refl => rewrite modSelf a in rewrite sym (plusSuccRightSucc a n) in sym (divAddSelf a n)

stepLeft : (h, a : Nat) -> LTE a h -> (n : Nat) ->
  b2n (modS h (a + h * 1) == 0) + divS h (modS h (S h `minus` modS h (a + h * 1)) + n)
    = divS h (modS h (S h `minus` a) + S n)
stepLeft h Z _ n = rewrite leftZero h in case h of
  Z => rewrite modSelf 0 in trans (cong S (divOne n)) (sym (divOne (S n)))
  S k => rewrite sym (minusOneSuccN k) in rewrite modSelf (S k) in
         rewrite modSmall {h = S k} {x = 1} (LTESucc (LTESucc LTEZero)) in Refl
stepLeft h (S m) le n = rewrite leftSucc h m le in case m of
  Z => rewrite modSelf h in rewrite minusZeroRight h in
       rewrite modSmall {h} {x = h} (LTESucc reflexive) in
       rewrite sym (plusSuccRightSucc h n) in sym (divAddSelf h n)
  S j => rewrite modSmall {h} (LTESucc (minusLte h j)) in
         rewrite modSmall {h} (LTESucc (minusLte h (S j))) in
         rewrite minusSucc h j (lteSuccLeft le) in
         cong (divS h) (plusSuccRightSucc (minus h (S j)) n)

-- One whole turn, click by click.
rightCount : {h : Nat} -> (d : Dial h) -> (n : Nat) ->
  zerosAfter d (replicate n (Right 1)) = zerosDuring d (Right n)
rightCount d Z = rewrite plusZeroRightNeutral (position d) in sym (divSmall (LTESucc (inRange d)))
rightCount d (S n) = Calc $
  |~ zerosAfter d (Right 1 :: replicate n (Right 1))
  ~~ b2n (isZero d') + zerosAfter d' (replicate n (Right 1)) ...(zerosAfterCons d (Right 1) _)
  ~~ b2n (isZero d') + zerosDuring d' (Right n)               ...(cong (b2n (isZero d') +) (rightCount d' n))
  ~~ divS h (position d + S n)                                 ...(stepRight h (position d) n (inRange d))
  where
    d' : Dial h
    d' = move d (Right 1)

leftCount : {h : Nat} -> (d : Dial h) -> (n : Nat) ->
  zerosAfter d (replicate n (Left 1)) = zerosDuring d (Left n)
leftCount d Z = rewrite plusZeroRightNeutral (modS h (S h `minus` position d)) in
  sym (divSmall (modBound h _))
leftCount d (S n) = Calc $
  |~ zerosAfter d (Left 1 :: replicate n (Left 1))
  ~~ b2n (isZero d') + zerosAfter d' (replicate n (Left 1)) ...(zerosAfterCons d (Left 1) _)
  ~~ b2n (isZero d') + zerosDuring d' (Left n)               ...(cong (b2n (isZero d') +) (leftCount d' n))
  ~~ zerosDuring d (Left (S n))                               ...(stepLeft h (position d) (inRange d) n)
  where
    d' : Dial h
    d' = move d (Left 1)

turnAt : {h : Nat} -> (d : Dial h) -> (t : Turn) -> foldl Day01.move d (clicks t) = move d t
turnAt d (Left n)  = dialExt _ _ (leftAt d n)
turnAt d (Right n) = dialExt _ _ (rightAt d n)

turnCount : {h : Nat} -> (d : Dial h) -> (t : Turn) -> zerosAfter d (clicks t) = zerosDuring d t
turnCount d (Left n)  = leftCount d n
turnCount d (Right n) = rightCount d n

zerosPassedFrom : {h : Nat} -> (d : Dial h) -> (ts : List Turn) ->
  zerosPassed d ts = zerosAfter d (allClicks ts)
zerosPassedFrom d [] = Refl
zerosPassedFrom d (t :: ts) = Calc $
  |~ zerosDuring d t + zerosPassed (move d t) ts
  ~~ zerosDuring d t + zerosAfter (move d t) rest              ...(cong (zerosDuring d t +) (zerosPassedFrom (move d t) ts))
  ~~ zerosAfter d (clicks t) + zerosAfter (move d t) rest      ...(cong (+ zerosAfter (move d t) rest) (sym (turnCount d t)))
  ~~ zerosAfter d (clicks t) + zerosAfter (foldl Day01.move d (clicks t)) rest
                                                                ...(cong (\e => zerosAfter d (clicks t) + zerosAfter e rest) (sym (turnAt d t)))
  ~~ zerosAfter d (clicks t ++ rest)                            ...(sym (zerosAfterAppend d (clicks t) rest))
  where
    rest : List Turn
    rest = allClicks ts

-- The arithmetic count is the click-by-click count, for any dial, start and turns.
zerosPassedCorrect : {h : Nat} -> (start : Dial h) -> (turns : List Turn) ->
  zerosPassed start turns = zerosPassedSpec start turns
zerosPassedCorrect = zerosPassedFrom

part2Puzzle : (turns : List Turn) -> solvePart2 turns = zerosPassedSpec Day01.dial turns
part2Puzzle = zerosPassedCorrect dial
