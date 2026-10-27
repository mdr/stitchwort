-- Day 8's circuit sizes, proved: the program's sizes, a histogram of the
-- boxes' labels (`Circuits.sizes`), are the spec's `circuitSizes` in another
-- order (`sizesPerm`, at the bottom), and an order makes no difference to
-- the product of the three largest (`threeLargestPerm`). Part1.sw uses both.
--
-- The argument:
--   1. Sorting, largest first, gives one list for any order of the sizes:
--      two sorted lists with the same elements are equal (`List.sortedPermEq`).
--   2. Two lists without repeats and with the same members are the same
--      elements in another order (`List.permOfSameMembers`).
--   3. The histogram's keys are the labels, without repeats (a map's keys
--      are in increasing order: `Map.keysDistinct`), and the value at each
--      label is how many boxes have it (`Map.getOrCounts`), never 0
--      (`Map.countsPositive`).
--   4. The spec counts each circuit at its first box: those boxes' labels
--      are the labels too, without repeats, and the size it counts at a
--      box is how many boxes have that box's label.

namespace Aoc.Day08.Proofs
import Aoc.Day08 (..)
import Aoc.Day08.Spec (..)
import Std (And, Bool, DecEq, Eq, List, Map, Nat, Ordering, Pair, Void)

-- Order makes no difference to the three largest ----------------------------

-- `x` may come before `y`, largest first.
def atLeast (x: Nat) (y: Nat): Bool := Nat.leq y x

theorem atLeastTrans (x: Nat) (y: Nat) (z: Nat) (h1: atLeast x y = True) (h2: atLeast y z = True): atLeast x z = True := omega

theorem atLeastAntisymm (x: Nat) (y: Nat) (h1: atLeast x y = True) (h2: atLeast y x = True): x = y := omega

-- Sorting largest first sorts by `atLeast`.
theorem sortedLargestFirst (xs: List Nat): List.Sorted atLeast (List.sortBy xs (a b => Nat.compare b a)) :=
  List.sortedCong (a b => Ordering.isLessEq (Nat.compare b a)) atLeast (a b => Nat.compareLeq b a) (List.sortBy xs (a b => Nat.compare b a))
    (List.sortBySorted (a b => Nat.compare b a) (a b h => rewrite Nat.compareLeq a b in rewrite Nat.compareLeq b a at h in omega) xs)

-- The three largest of the same sizes in any order.
theorem threeLargestPerm (xs: List Nat) (ys: List Nat) (p: List.Perm xs ys): threeLargestProduct xs = threeLargestProduct ys :=
  let sortX := List.sortBy xs (a b => Nat.compare b a)
  let sortY := List.sortBy ys (a b => Nat.compare b a)
  Eq.cong (sorted => List.product (List.take sorted 3))
    (List.sortedPermEq atLeast atLeastTrans atLeastAntisymm sortX sortY (sortedLargestFirst xs) (sortedLargestFirst ys)
      (List.permTrans sortX xs sortY (List.sortByPerm xs _) (List.permTrans xs ys sortY p (List.permSym sortY ys (List.sortByPerm ys _)))))

-- The histogram's keys --------------------------------------------------------

-- How many of the boxes 0 to n - 1 have the label.
def labelCount (c: Circuits) (n: Nat) (label: Nat): Nat := List.count (List.map (List.range n) c.labelOf) (x => x == label)

-- The histogram of the labels.
def labelCounts (c: Circuits) (n: Nat): Map Nat Nat := Map.counts (List.map (List.range n) c.labelOf)

theorem getOrLabelCounts (c: Circuits) (n: Nat) (label: Nat): Map.getOr (labelCounts c n) label 0 = labelCount c n label :=
  rewrite Map.getOrCounts label (List.map (List.range n) c.labelOf), Map.Spec.sameKeyDecide label _ in rfl

-- Each entry of the histogram is a label and its count.
theorem entryCount (c: Circuits) (n: Nat): (e: (Nat, Nat)) → List.Mem e (Map.toList (labelCounts c n)) → e.snd = labelCount c n e.fst
  | (label, v), m =>
    Eq.trans (Eq.sym (Eq.cong (.getOrElse 0) ((Map.memToList (labelCounts c n) label v).forward m))) (getOrLabelCounts c n label)

-- A label is counted once at least exactly when some box has it.
theorem memOfCount (c: Circuits) (n: Nat) (label: Nat) (h: 0 < labelCount c n label): List.Mem label (List.map (List.range n) c.labelOf) :=
  List.anyTrueElim (List.map (List.range n) c.labelOf) (x => x == label) (List.Mem label (List.map (List.range n) c.labelOf))
    (rewrite List.anyOccurrences (List.map (List.range n) c.labelOf) (x => x == label), <- List.countOccurrences _ (x => x == label) in h)
    (x m e => rewrite <- DecEq.sound x label e in m)

theorem countOfMem (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (List.map (List.range n) c.labelOf)): 0 < labelCount c n label :=
  rewrite List.countOccurrences _ (x => x == label), <- List.anyOccurrences _ (x => x == label) in
    List.anyOfMem (List.map (List.range n) c.labelOf) (x => x == label) label (DecEq.refl label) m

-- The histogram's keys are the labels.
theorem keyOfLabel (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (List.map (List.range n) c.labelOf)):
    List.Mem label (Map.keys (labelCounts c n)) :=
  let positive: 0 < Map.getOr (labelCounts c n) label 0 := rewrite getOrLabelCounts c n label in countOfMem c n label m
  match g: Map.get (labelCounts c n) label with
    | None => Void.exfalso (Bool.falseNotTrue positive)
    | Some v => List.memMap (Map.toList (labelCounts c n)) (label, v) ((Map.memToList (labelCounts c n) label v).backward g) Pair.fst

theorem labelOfKey (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (Map.keys (labelCounts c n))):
    List.Mem label (List.map (List.range n) c.labelOf) :=
  List.anyElim ((e: (Nat, Nat)) => e.fst = label) (List.Mem label (List.map (List.range n) c.labelOf)) (Map.toList (labelCounts c n))
    (List.memMapAny (Map.toList (labelCounts c n)) Pair.fst label m)
    (e me key =>
      let positive: 0 < e.snd :=
        match e with
          | (k, v) =>
            Map.countsPositive (List.map (List.range n) c.labelOf) k v
              ((Map.memToList (labelCounts c n) k v).forward me)
      rewrite <- key in memOfCount c n e.fst (rewrite <- entryCount c n e me in positive))

-- The histogram's values are the counts of its keys.
theorem valuesAreCounts (c: Circuits) (n: Nat): c.sizes n = List.map (Map.keys (labelCounts c n)) (labelCount c n) :=
  rewrite List.mapMap (Map.toList (labelCounts c n)) (labelCount c n) Pair.fst in
    List.mapCongMem (Map.toList (labelCounts c n)) Pair.snd (e => labelCount c n e.fst) (entryCount c n)

-- The spec's first boxes -----------------------------------------------------

-- No lower box has b's label: the spec counts b's circuit at b.
def firstBox (c: Circuits) (b: Nat): Bool := ¬(List.range b |> .any (other => c.labelOf other == c.labelOf b))

-- The labels of the first boxes don't repeat ...
theorem firstsDistinct (c: Circuits): (k: Nat) → (s: Nat) → List.Distinct (List.map (List.filter (List.rangeFrom k s) (firstBox c)) c.labelOf)
  | Zero, s => Trivial
  | Succ k, s =>
    match e: firstBox c s with
      | True =>
        Both
          (m =>
            List.anyElim (b => c.labelOf b = c.labelOf s) Void (List.filter (List.rangeFrom k (Succ s)) (firstBox c))
              (List.memMapAny _ c.labelOf (c.labelOf s) m)
              (b mb same =>
                match List.memFilter (List.rangeFrom k (Succ s)) (firstBox c) b mb with
                  | Both inRange first =>
                    let lower: List.any (List.range b) (other => c.labelOf other == c.labelOf b) = True :=
                      List.anyRangeIntro (other => c.labelOf other == c.labelOf b) b 0 s omega
                        (omega [List.memRangeFrom b k (Succ s) inRange]) (rewrite same, DecEq.refl (c.labelOf s) in rfl)
                    Bool.falseNotTrue (rewrite lower at first)))
          (firstsDistinct c k (Succ s))
      | False => firstsDistinct c k (Succ s)

-- ... and they are all the labels: each box's label is a first box's.
theorem firstOf (c: Circuits) (n: Nat): (fuel: Nat) → (b: Nat) → b < fuel → b < n →
    List.Mem (c.labelOf b) (List.map (List.filter (List.range n) (firstBox c)) c.labelOf)
  | Zero, b, h, hb => Void.exfalso (Bool.falseNotTrue h)
  | Succ fuel, b, h, hb =>
    match g: List.any (List.range b) (other => c.labelOf other == c.labelOf b) with
      | False =>
        List.memMap _ b (List.memFilterIntro (List.range n) (firstBox c) b (List.memRangeFromIntro b n 0 omega hb) (rewrite g in rfl)) c.labelOf
      | True =>
        List.anyTrueElim (List.range b) (other => c.labelOf other == c.labelOf b)
          (List.Mem (c.labelOf b) (List.map (List.filter (List.range n) (firstBox c)) c.labelOf)) g
          (other mo same =>
            let below := List.memRangeFrom other b 0 mo
            rewrite <- DecEq.sound (c.labelOf other) (c.labelOf b) same in firstOf c n fuel other omega omega)

theorem labelOfFirst (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (List.map (List.filter (List.range n) (firstBox c)) c.labelOf)):
    List.Mem label (List.map (List.range n) c.labelOf) :=
  List.anyElim (b => c.labelOf b = label) (List.Mem label (List.map (List.range n) c.labelOf)) (List.filter (List.range n) (firstBox c))
    (List.memMapAny _ c.labelOf label m)
    (b mb e => rewrite <- e in List.memMap (List.range n) b (And.left (List.memFilter (List.range n) (firstBox c) b mb)) c.labelOf)

theorem firstOfLabel (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (List.map (List.range n) c.labelOf)):
    List.Mem label (List.map (List.filter (List.range n) (firstBox c)) c.labelOf) :=
  List.anyElim (b => c.labelOf b = label) (List.Mem label (List.map (List.filter (List.range n) (firstBox c)) c.labelOf)) (List.range n)
    (List.memMapAny _ c.labelOf label m)
    (b mb e => rewrite <- e in firstOf c n (Succ b) b omega (And.right (List.memRangeFrom b n 0 mb)))

-- The spec's sizes, with "same label" as the test, are the counts of the
-- first boxes' labels.
theorem circuitSizesAreCounts (c: Circuits) (n: Nat):
    circuitSizes n (a b => c.labelOf a == c.labelOf b) = List.map (List.map (List.filter (List.range n) (firstBox c)) c.labelOf) (labelCount c n) :=
  rewrite List.mapMap _ (labelCount c n) c.labelOf, List.countMap (List.range n) (x => x == c.labelOf _) c.labelOf in rfl

-- The program's sizes are the spec's, in another order.
theorem sizesPerm (c: Circuits) (n: Nat): List.Perm (c.sizes n) (circuitSizes n (a b => c.labelOf a == c.labelOf b)) :=
  rewrite valuesAreCounts c n, circuitSizesAreCounts c n in
    List.permMap (Map.keys (labelCounts c n)) (List.map (List.filter (List.range n) (firstBox c)) c.labelOf)
      (List.permOfSameMembers (Map.keys (labelCounts c n)) (List.map (List.filter (List.range n) (firstBox c)) c.labelOf)
        (Map.keysDistinct (labelCounts c n))
        (firstsDistinct c n 0)
        (label m => firstOfLabel c n label (labelOfKey c n label m))
        (label m => keyOfLabel c n label (labelOfFirst c n label m)))
      (labelCount c n)
