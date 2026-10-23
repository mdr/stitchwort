-- Day 8, part 1, proved for every list of boxes and every number of
-- connections (`part1Correct`, at the bottom): the program's answer is the
-- product of the three largest circuits of Proofs/Spec.sw. The argument:
--   1. The program's sorted pairs are the spec's connection order, each
--      with its key (`closestFirstIsOrder`): numbering the boxes and taking
--      every pair is `allPairs`, and sorting the keyed pairs is sorting the
--      pairs by their keys (`List.sortOnMap`).
--   2. So the program joins exactly the first k connections, and by the
--      label theorem (Labels.sw) its labels tell which boxes are joined.
--   3. The program's sizes are `circuitSizes` with "same label" as the test
--      (`sizesAreCircuitSizes`), and any two tests that tell give the same
--      sizes (`circuitSizesCong`).

namespace Aoc.Day08.Proofs
import Aoc.Day08 (..)
import Std (And, Bool, Eq, List, Nat, Ord, Ordering, Pair, Void)

-- The program's order is the spec's ----------------------------------------

-- The program's pairs, closest first, are the spec's connections in order,
-- each with its key: sorting the keys is sorting the pairs by their keys.
theorem closestFirstIsOrder (points: List Point): closestFirst points = List.map (connectionKey points) (connectionOrder points) :=
  calc closestFirst points
    _ = List.sort (List.map (connectionKey points) (allPairs points.length)) :=
      rewrite List.withIndexRange origin points, List.pairsMap (i => (i, List.getOr origin i points)) (List.range points.length),
        List.mapMap _ _ (List.pairs (List.range points.length))
        in rfl
    _ = List.map (connectionKey points) (connectionOrder points) := Eq.sym (List.sortOnMap (connectionKey points) (allPairs points.length))

-- The program's fold joins the first k connections.
theorem joinedIsJoinAll (k: Nat) (points: List Point):
    List.foldLeft Circuits.connect (Circuits.separate points.length) (List.take k (closestFirst points))
      = joinAll (Circuits.separate points.length) (firstConnections k points) :=
  rewrite closestFirstIsOrder points, List.takeMap (connectionKey points) k (connectionOrder points),
    List.foldLeftMap Circuits.connect (connectionKey points) (Circuits.separate points.length) (List.take k (connectionOrder points))
    in rfl

-- Every connection is between two of the boxes ------------------------------

theorem allAppend (p: a -> Bool): (xs: List a) -> (ys: List a) -> List.all p xs = True -> List.all p ys = True -> List.all p (List.append xs ys) = True
  | Nil, ys, hx, hy => hy
  | Cons x xs, ys, hx, hy =>
    match e: p x with
      | True => allAppend p xs ys hx hy
      | False => hx

theorem allTake (p: a -> Bool): (k: Nat) -> (xs: List a) -> List.all p xs = True -> List.all p (List.take k xs) = True
  | Zero, xs, h => rfl
  | Succ k, Nil, h => rfl
  | Succ k, Cons x xs, h =>
    match e: p x with
      | True => allTake p k xs h
      | False => h

-- If every element passes q, so do both ends of every pair.
theorem allPairsBoth (q: Nat -> Bool): (xs: List Nat) -> List.all q xs = True -> List.all (pair => q pair.fst && q pair.snd) (List.pairs xs) = True
  | Nil, h => rfl
  | Cons x xs, h =>
    match e: q x with
      | True => allAppend _ (List.map (y => (x, y)) xs) (List.pairs xs) (allMapPairWith q x e xs h) (allPairsBoth q xs h)
      | False => Void.exfalso (Bool.falseNotTrue h)

theorem allMapPairWith (q: Nat -> Bool) (x: Nat) (hx: q x = True): (xs: List Nat) -> List.all q xs = True ->
    List.all (pair => q pair.fst && q pair.snd) (List.map (y => (x, y)) xs) = True
  | Nil, h => rfl
  | Cons y ys, h =>
    match e: q y with
      | True => rewrite hx in allMapPairWith q x hx ys h
      | False => Void.exfalso (Bool.falseNotTrue h)

theorem connectionsInRange (k: Nat) (points: List Point): List.all (boxesBelow points.length) (firstConnections k points) = True :=
  let n := points.length
  let below: List.all (i => Nat.leq (Succ i) n) (List.range n) = True :=
    List.allRangeIntro (i => Nat.leq (Succ i) n) n 0 (i lo hi => hi)
  allTake (boxesBelow n) k (connectionOrder points)
    (rewrite List.allPerm (boxesBelow n) (connectionOrder points) (allPairs n)
      (List.sortOnPerm (connectionKey points) (allPairs n))
      in allPairsBoth (i => Nat.leq (Succ i) n) (List.range n) below)

-- The program's sizes are the spec's ----------------------------------------

-- Counted with "same label" as the test, the spec's sizes are the program's.
theorem sizesAreCircuitSizes (c: Circuits) (n: Nat): c.sizes n = circuitSizes n (a b => c.labelOf a == c.labelOf b) :=
  rewrite List.filterCongMem
      (box => !(List.any (label => label == c.labelOf box) (List.take box (List.map c.labelOf (List.range n)))))
      (box => !(List.any (other => c.labelOf other == c.labelOf box) (List.range box)))
      (List.range n)
      (box m =>
        rewrite List.takeMap c.labelOf box (List.range n), List.takeRangeFrom box n 0 (omega [And.right (List.memRangeFrom box n 0 m)]),
          List.anyMap (label => label == c.labelOf box) c.labelOf (List.range box) in rfl)
    in List.mapCong _ _ _ (box => List.countMap (label => label == c.labelOf box) c.labelOf (List.range n))

-- Two tests that agree on the boxes give the same sizes.
theorem circuitSizesCong (n: Nat) (same1: Nat -> Nat -> Bool) (same2: Nat -> Nat -> Bool)
    (agree: (a: Nat) -> (b: Nat) -> a < n -> b < n -> same1 a b = same2 a b): circuitSizes n same1 = circuitSizes n same2 :=
  let below: (x: Nat) -> List.Mem x (List.range n) -> x < n := x m => And.right (List.memRangeFrom x n 0 m)
  rewrite List.filterCongMem
      (box => !(List.any (other => same1 other box) (List.range box)))
      (box => !(List.any (other => same2 other box) (List.range box)))
      (List.range n)
      (box m =>
        rewrite List.anyCongMem (other => same1 other box) (other => same2 other box) (List.range box)
          (other m2 => agree other box (omega [And.right (List.memRangeFrom other box 0 m2), below box m]) (below box m))
          in rfl)
    in List.mapCongMem _ _ _
      (box m => List.countCongMem (other => same1 other box) (other => same2 other box) (List.range n)
        (other m2 => agree other box (below other m2) (below box (And.left (List.memFilter _ box (List.range n) m)))))

-- Two tests that tell agree.
theorem tellersAgree (n: Nat) (connections: List (Nat, Nat)) (same1: Nat -> Nat -> Bool) (same2: Nat -> Nat -> Bool)
    (t1: Tells n connections same1) (t2: Tells n connections same2) (a: Nat) (b: Nat) (ha: a < n) (hb: b < n): same1 a b = same2 a b :=
  Bool.eqOf (same1 a b) (same2 a b)
    (s => (t2 a b ha hb).backward ((t1 a b ha hb).forward s))
    (s => (t1 a b ha hb).backward ((t2 a b ha hb).forward s))

-- Part 1 is right: for every list of boxes and every k, the program's
-- answer is the product of the three largest circuits after the first k
-- connections, whatever test is used to tell the circuits.
theorem part1Correct (k: Nat) (points: List Point) (sameCircuit: Nat -> Nat -> Bool)
    (tells: Tells points.length (firstConnections k points) sameCircuit):
    solvePart1 k (Boxes.of points) = threeLargestProduct (circuitSizes points.length sameCircuit) :=
  let n := points.length
  let joined := joinAll (Circuits.separate n) (firstConnections k points)
  calc solvePart1 k (Boxes.of points)
    _ = threeLargestProduct (joined.sizes n) := rewrite <- joinedIsJoinAll k points in rfl
    _ = threeLargestProduct (circuitSizes n (a b => joined.labelOf a == joined.labelOf b)) := rewrite sizesAreCircuitSizes joined n in rfl
    _ = threeLargestProduct (circuitSizes n sameCircuit) :=
      rewrite circuitSizesCong n (a b => joined.labelOf a == joined.labelOf b) sameCircuit
        (tellersAgree n (firstConnections k points) _ sameCircuit (labelsTell n (firstConnections k points) (connectionsInRange k points)) tells)
        in rfl
