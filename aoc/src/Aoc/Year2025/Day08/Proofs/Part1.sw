--| Day 8, part 1, proved for every list of boxes and every number of
--| connections (`part1Correct`, at the bottom): the program's answer is the
--| product of the three largest circuits of Spec/Spec.sw.
--
-- The argument:
--   1. The program's sorted pairs are the spec's connection order, each
--      with its key (`closestFirstIsOrder`): numbering the boxes and taking
--      every pair is `allPairs`, and sorting the keyed pairs is sorting the
--      pairs by their keys (`List.sortOnMap`).
--   2. So the program joins exactly the first k connections, and by the
--      label theorem (Labels.sw) its labels tell which boxes are joined.
--   3. The program's sizes are `circuitSizes` with "same label" as the test,
--      in another order (`sizesPerm`, Sizes.sw), which the three largest
--      don't depend on (`threeLargestPerm`); and any two tests that tell
--      give the same sizes (`circuitSizesCongRange`).

namespace Aoc.Year2025.Day08.Proofs
import Aoc.Year2025.Day08 (..)
import Aoc.Year2025.Day08.Spec (..)
import Std (And, Bool, Eq, List, Nat, Ord, Ordering, Pair, Void)

-- The program's order is the spec's ----------------------------------------

--| The program's pairs, closest first, are the spec's connections in order,
--| each with its key: sorting the keys is sorting the pairs by their keys.
theorem closestFirstIsOrder (points: List Point): closestFirst points = List.map (connectionOrder points) (connectionKey points) :=
  calc closestFirst points
    _ = List.sort (List.map (allPairs points.length) (connectionKey points)) :=
      rewrite List.withIndexRange points Point.origin, List.pairsMap (List.range 0 points.length) (i => (i, List.getOr points i Point.origin)),
        List.mapMap (List.pairs (List.range 0 points.length)) _ _
        in rfl
    _ = List.map (connectionOrder points) (connectionKey points) := Eq.sym (List.sortOnMap (allPairs points.length) (connectionKey points))

--| The program's fold joins the first k connections.
theorem joinedIsJoinAll (k: Nat) (points: List Point):
    List.foldLeft (List.take (closestFirst points) k) (Circuits.separate points.length) Circuits.connect
      = joinAll (Circuits.separate points.length) (firstConnections k points) :=
  rewrite closestFirstIsOrder points, List.takeMap (connectionOrder points) k (connectionKey points),
    List.foldLeftMap (List.take (connectionOrder points) k) (Circuits.separate points.length) Circuits.connect (connectionKey points)
    in rfl

-- Every connection is between two of the boxes ------------------------------

theorem allAppend (p: a → Bool) (xs ys: List a) (hx: xs.all p = True) (hy: ys.all p = True): (xs.append ys).all p = True :=
  match xs with
    | [] => hy
    | [x, ..xs] =>
      match e: p x with
        | True => allAppend p xs ys hx hy

theorem allTake (p: a → Bool) (k: Nat) (xs: List a) (h: xs.all p = True): (xs.take k).all p = True :=
  match k, xs with
    | Zero, xs => rfl
    | Succ k, [] => rfl
    | Succ k, [x, ..xs] =>
      match e: p x with
        | True => allTake p k xs h

--| If every element passes q, so do both ends of every pair.
theorem allPairsBoth (q: Nat → Bool) (xs: List Nat) (h: xs.all q = True): xs.pairs.all (pair => q pair.fst ∧ q pair.snd) = True :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      match e: q x with
        | True => allAppend _ (List.map xs (y => (x, y))) (List.pairs xs) (allMapPairWith q x e xs h) (allPairsBoth q xs h)

theorem allMapPairWith (q: Nat → Bool) (x: Nat) (hx: q x = True) (xs: List Nat) (h: xs.all q = True):
    (xs.map (y => (x, y))).all (pair => q pair.fst ∧ q pair.snd) = True :=
  match xs with
    | [] => rfl
    | [y, ..ys] =>
      match e: q y with
        | True => rewrite hx in allMapPairWith q x hx ys h

theorem connectionsInRange (k: Nat) (points: List Point): List.all (firstConnections k points) (boxesBelow points.length) = True :=
  let n := points.length
  let below: List.all (List.range 0 n) (i => Nat.leq (Succ i) n) = True :=
    List.allRangeIntro (i => Nat.leq (Succ i) n) n 0 (i lo hi => hi)
  allTake (boxesBelow n) k (connectionOrder points)
    (rewrite List.allPerm (connectionOrder points) (allPairs n) (List.sortOnPerm (allPairs n) (connectionKey points))
      (boxesBelow n)
      in allPairsBoth (i => Nat.leq (Succ i) n) (List.range 0 n) below)

-- The program's sizes are the spec's ----------------------------------------

--| Two tests that agree on the boxes give the same sizes.
theorem circuitSizesCongRange (n: Nat) (same1: Nat → Nat → Bool) (same2: Nat → Nat → Bool)
    (agree: ∀ (a b: Nat) => a < n → b < n → same1 a b = same2 a b): circuitSizes n same1 = circuitSizes n same2 :=
  let below: ∀ (x: Nat) => List.Mem x (List.range 0 n) → x < n := x m => And.right (List.memRangeFrom x n 0 m)
  rewrite agree, agree _ _ _ (below _ (And.left (List.memFilter (List.range 0 n) _ _)))

--| Two tests that tell agree.
theorem tellersAgree (n: Nat) (connections: List (Nat, Nat)) (same1: Nat → Nat → Bool) (same2: Nat → Nat → Bool)
    (t1: Tells n connections same1) (t2: Tells n connections same2) (a: Nat) (b: Nat) (ha: a < n) (hb: b < n): same1 a b = same2 a b :=
  Bool.eqOf (same1 a b) (same2 a b)
    (s => (t2 a b ha hb).backward ((t1 a b ha hb).forward s))
    (s => (t1 a b ha hb).backward ((t2 a b ha hb).forward s))

--| Part 1 is right: for every list of boxes and every k, the program's
--| answer is the product of the three largest circuits after the first k
--| connections, whatever test is used to tell the circuits.
theorem part1Correct (k: Nat) (points: List Point) (sameCircuit: Nat → Nat → Bool)
    (tells: Tells points.length (firstConnections k points) sameCircuit):
    solvePart1 k (Boxes.of points) = threeLargestProduct (circuitSizes points.length sameCircuit) :=
  let n := points.length
  let joined := joinAll (Circuits.separate n) (firstConnections k points)
  calc solvePart1 k (Boxes.of points)
    _ = threeLargestProduct (joined.sizes n) := rewrite <- joinedIsJoinAll k points in rfl
    _ = threeLargestProduct (circuitSizes n (a b => joined.labelOf a == joined.labelOf b)) :=
      threeLargestPerm (joined.sizes n) (circuitSizes n (a b => joined.labelOf a == joined.labelOf b)) (sizesPerm joined n)
    _ = threeLargestProduct (circuitSizes n sameCircuit) :=
      rewrite circuitSizesCongRange n (a b => joined.labelOf a == joined.labelOf b) sameCircuit
        (tellersAgree n (firstConnections k points) _ sameCircuit (labelsTell n (firstConnections k points) (connectionsInRange k points)) tells)
        in rfl
