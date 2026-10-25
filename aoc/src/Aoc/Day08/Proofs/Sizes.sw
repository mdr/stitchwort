-- Day 8's circuit sizes, proved: the program's sizes, a histogram of the
-- boxes' labels (`Circuits.sizes`), are the spec's `circuitSizes` in another
-- order (`sizesPerm`, at the bottom), and an order makes no difference to
-- the product of the three largest (`threeLargestPerm`). Part1.sw uses both.
--
-- The argument:
--   1. Sorting, largest first, gives one list for any order of the sizes:
--      two sorted lists with the same elements are equal (`sortedDescUnique`).
--   2. Two lists without repeats and with the same members are the same
--      elements in another order (`permOfSameMembers`).
--   3. The histogram's keys are the labels, without repeats (a map's keys
--      are in increasing order), and the value at each label is how many
--      boxes have it (`Map.getOrCounts`), never 0.
--   4. The spec counts each circuit at its first box: those boxes' labels
--      are the labels too, without repeats, and the size it counts at a
--      box is how many boxes have that box's label.

namespace Aoc.Day08.Proofs
import Aoc.Day08 (..)
import Aoc.Day08.Spec (..)
import Std (And, Bool, DecEq, Eq, List, Map, Nat, Option, Ord, Ordering, Pair, Void)

-- Order makes no difference to the three largest ----------------------------

-- `x` may come before `y`, largest first.
def atLeast (x: Nat) (y: Nat): Bool := Nat.leq y x

theorem atLeastTrans (x: Nat) (y: Nat) (z: Nat) (h1: atLeast x y = True) (h2: atLeast y z = True): atLeast x z = True := omega

-- Two lists sorted largest first with the same elements are equal.
theorem sortedDescUnique: (xs: List Nat) -> (ys: List Nat) -> List.Sorted atLeast xs -> List.Sorted atLeast ys -> List.Perm xs ys -> xs = ys
  | Nil, Nil, sx, sy, p => rfl
  | Nil, Cons y ys, sx, sy, p => omega [List.permLength Nil (Cons y ys) p]
  | Cons x xs, Nil, sx, sy, p => omega [List.permLength (Cons x xs) Nil p]
  | Cons x xs, Cons y ys, Both hx sx, Both hy sy, p =>
    let same: x = y :=
      match List.memPerm (Cons y ys) (Cons x xs) (List.permSym (Cons x xs) (Cons y ys) p) y (Inl rfl) with
        | Inl e => e
        | Inr my =>
          match List.memPerm (Cons x xs) (Cons y ys) p x (Inl rfl) with
            | Inl e => Eq.sym e
            | Inr mx =>
              let xy := List.sortedHeadLe atLeast atLeastTrans x y xs (Both hx sx) my
              let yx := List.sortedHeadLe atLeast atLeastTrans y x ys (Both hy sy) mx
              omega
    let rest: xs = ys := sortedDescUnique xs ys sx sy (q => omega [p q, Eq.cong (z => Bool.toNat (q z)) same])
    rewrite same, rest in rfl

-- Sorting largest first sorts by `atLeast`.
theorem sortedLargestFirst (xs: List Nat): List.Sorted atLeast (List.sortBy xs (a b => Nat.compare b a)) :=
  List.sortedCong (a b => Ordering.isLessEq (Nat.compare b a)) atLeast (a b => Nat.compareLeq b a) (List.sortBy xs (a b => Nat.compare b a))
    (List.sortBySorted (a b => Nat.compare b a) (a b h => rewrite Nat.compareLeq a b in rewrite Nat.compareLeq b a at h in omega) xs)

-- The three largest of the same sizes in any order.
theorem threeLargestPerm (xs: List Nat) (ys: List Nat) (p: List.Perm xs ys): threeLargestProduct xs = threeLargestProduct ys :=
  let sortX := List.sortBy xs (a b => Nat.compare b a)
  let sortY := List.sortBy ys (a b => Nat.compare b a)
  Eq.cong (sorted => List.product (List.take sorted 3))
    (sortedDescUnique sortX sortY (sortedLargestFirst xs) (sortedLargestFirst ys)
      (List.permTrans sortX xs sortY (List.sortByPerm xs _) (List.permTrans xs ys sortY p (List.permSym sortY ys (List.sortByPerm ys _)))))

-- Lists without repeats with the same members ------------------------------

theorem occurrencesMap (q: b -> Bool) (f: a -> b): (xs: List a) -> List.occurrences (List.map xs f) q = List.occurrences xs (x => q (f x))
  | Nil => rfl
  | Cons x xs => rewrite occurrencesMap q f xs in rfl

theorem permMap (f: a -> b) (xs: List a) (ys: List a) (p: List.Perm xs ys): List.Perm (List.map xs f) (List.map ys f) :=
  q => rewrite occurrencesMap q f xs, occurrencesMap q f ys in p (x => q (f x))

theorem occurrencesFilter (q: a -> Bool) (r: a -> Bool): (xs: List a) -> List.occurrences (List.filter xs r) q = List.occurrences xs (x => q x && r x)
  | Nil => rfl
  | Cons x xs =>
    match e: r x with
      | True => rewrite occurrencesFilter q r xs, Bool.andTrue (q x) in rfl
      | False => rewrite occurrencesFilter q r xs, Bool.andFalse (q x) in rfl

theorem distinctFilter (r: a -> Bool): (xs: List a) -> List.Distinct xs -> List.Distinct (List.filter xs r)
  | Nil, d => Trivial
  | Cons x xs, Both notMem d =>
    match e: r x with
      | True => Both (m => notMem (And.left (List.memFilter xs r x m))) (distinctFilter r xs d)
      | False => distinctFilter r xs d

-- Counting q at x in a list without x ...
theorem occurrencesAbsent (q: Nat -> Bool) (x: Nat): (ys: List Nat) -> Not (List.Mem x ys) -> List.occurrences ys (z => q z && (z == x)) = 0
  | Nil, n => rfl
  | Cons y ys, n =>
    match e: y == x with
      | True => Void.exfalso (n (Inl (eqTrue y x e)))
      | False => rewrite Bool.andFalse (q y), occurrencesAbsent q x ys (m => n (Inr m)) in rfl

-- ... and in a list with x once.
theorem occurrencesOnce (q: Nat -> Bool) (x: Nat): (ys: List Nat) -> List.Distinct ys -> List.Mem x ys ->
    List.occurrences ys (z => q z && (z == x)) = Bool.toNat (q x)
  | Nil, d, m => Void.exfalso m
  | Cons y ys, Both notMem d, Inl e =>
    rewrite e, eqSelf x, Bool.andTrue (q x), occurrencesAbsent q x ys (rewrite e at notMem) in omega
  | Cons y ys, Both notMem d, Inr m =>
    match e: y == x with
      | True => Void.exfalso (notMem (rewrite eqTrue y x e in m))
      | False => rewrite Bool.andFalse (q y), occurrencesOnce q x ys d m in rfl

-- Two lists of numbers without repeats and with the same members are the
-- same numbers in another order.
theorem permOfSameMembers: (xs: List Nat) -> (ys: List Nat) -> List.Distinct xs -> List.Distinct ys ->
    ((x: Nat) -> List.Mem x xs -> List.Mem x ys) -> ((y: Nat) -> List.Mem y ys -> List.Mem y xs) -> List.Perm xs ys
  | Nil, Nil, dx, dy, there, back, q => rfl
  | Nil, Cons y ys, dx, dy, there, back, q => Void.exfalso (back y (Inl rfl))
  | Cons x xs, ys, Both notMem dx, dy, there, back, q =>
    let others := List.filter ys (z => !(z == x))
    let rest: List.occurrences xs q = List.occurrences others q :=
      permOfSameMembers xs others dx (distinctFilter (z => !(z == x)) ys dy)
        (z m =>
          List.memFilterIntro ys (z => !(z == x)) z (there z (Inr m))
            (match e: z == x with
              | True => Void.exfalso (notMem (rewrite <- eqTrue z x e in m))
              | False => rfl))
        (z m =>
          match List.memFilter ys (z => !(z == x)) z m with
            | Both inYs notX =>
              match back z inYs with
                | Inl e => Void.exfalso (Bool.falseNotTrue (rewrite e, eqSelf z at notX))
                | Inr inXs => inXs)
        q
    rewrite occurrencesSplit q x ys, occurrencesOnce q x ys dy (there x (Inl rfl)), <- occurrencesFilter q (z => !(z == x)) ys, <- rest
      in omega

-- The histogram's keys --------------------------------------------------------

-- Every key of an increasing list is above its lower bound ...
theorem keysAbove (ord: Ord k) (key: k): (lo: Option k) -> (xs: List (k, v)) -> Map.Spec.Ascending ord lo xs ->
    List.Mem key (List.map xs Pair.fst) -> Map.Tree.Above ord lo key
  | lo, Nil, asc, m => Void.exfalso m
  | lo, Cons (kk, vv) rest, Both above arest, Inl e => rewrite <- e in above
  | None, Cons (kk, vv) rest, Both above arest, Inr m => Trivial
  | Some low, Cons (kk, vv) rest, Both above arest, Inr m => ord.trans low kk key above (keysAbove ord key (Some kk) rest arest m)

-- ... so the keys don't repeat.
theorem keysDistinct (ord: Ord k): (lo: Option k) -> (xs: List (k, v)) -> Map.Spec.Ascending ord lo xs -> List.Distinct (List.map xs Pair.fst)
  | lo, Nil, asc => Trivial
  | lo, Cons (kk, vv) rest, Both above arest =>
    Both (m => Ordering.lessNotEqual (Eq.trans (Eq.sym (keysAbove ord kk (Some kk) rest arest m)) (Ord.compareSelf kk)))
      (keysDistinct ord (Some kk) rest arest)

-- No count is 0.
theorem countsPositive (key: Nat): (xs: List Nat) -> (m: Map Nat Nat) -> ((v: Nat) -> Map.get m key = Some v -> 0 < v) ->
    (v: Nat) -> Map.get (List.foldLeft xs m (acc x => Map.insertWith acc x 1 Nat.add)) key = Some v -> 0 < v
  | Nil, m, h, v, found => h v found
  | Cons x rest, m, h, v, found =>
    countsPositive key rest (Map.insertWith m x 1 Nat.add) (v g =>
      match e: key == x with
        | True =>
          let inserted := rewrite eqTrue key x e, Map.getInsertWith m x 1 Nat.add at g
          match c: Map.get m x with
            | None => rewrite <- Option.someInjective _ v inserted in rfl
            | Some old => rewrite <- Option.someInjective _ v inserted in omega
        | False => h v (rewrite Map.getInsertWithOther m x 1 key (DecEq.soundFalse key x e) Nat.add at g))
      v found

-- How many of the boxes 0 to n - 1 have the label.
def labelCount (c: Circuits) (n: Nat) (label: Nat): Nat := List.count (List.map (List.range n) c.labelOf) (x => x == label)

-- The histogram of the labels.
def labelCounts (c: Circuits) (n: Nat): Map Nat Nat := Map.counts (List.map (List.range n) c.labelOf)

theorem getOrLabelCounts (c: Circuits) (n: Nat) (label: Nat): Map.getOr (labelCounts c n) 0 label = labelCount c n label :=
  rewrite Map.getOrCounts label (List.map (List.range n) c.labelOf), Map.Spec.sameKeyDecide label _ in rfl

-- Each entry of the histogram is a label and its count.
theorem entryCount (c: Circuits) (n: Nat): (e: (Nat, Nat)) -> List.Mem e (Map.toList (labelCounts c n)) -> e.snd = labelCount c n e.fst
  | (label, v), m =>
    Eq.trans (Eq.sym (Eq.cong (.getOrElse 0) ((Map.memToList (labelCounts c n) label v).forward m))) (getOrLabelCounts c n label)

-- A label is counted once at least exactly when some box has it.
theorem memOfCount (c: Circuits) (n: Nat) (label: Nat) (h: 0 < labelCount c n label): List.Mem label (List.map (List.range n) c.labelOf) :=
  List.anyTrueElim (List.map (List.range n) c.labelOf) (x => x == label) (List.Mem label (List.map (List.range n) c.labelOf))
    (rewrite List.anyOccurrences (List.map (List.range n) c.labelOf) (x => x == label), <- List.countOccurrences _ (x => x == label) in h)
    (x m e => rewrite <- eqTrue x label e in m)

theorem countOfMem (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (List.map (List.range n) c.labelOf)): 0 < labelCount c n label :=
  rewrite List.countOccurrences _ (x => x == label), <- List.anyOccurrences _ (x => x == label) in
    List.anyOfMem (List.map (List.range n) c.labelOf) (x => x == label) label (eqSelf label) m

-- The histogram's keys are the labels.
theorem keyOfLabel (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (List.map (List.range n) c.labelOf)):
    List.Mem label (Map.keys (labelCounts c n)) :=
  let positive: 0 < Map.getOr (labelCounts c n) 0 label := rewrite getOrLabelCounts c n label in countOfMem c n label m
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
            countsPositive k (List.map (List.range n) c.labelOf) Map.empty (v g => Void.exfalso (Option.noneNotSome v g)) v
              ((Map.memToList (labelCounts c n) k v).forward me)
      rewrite <- key in memOfCount c n e.fst (rewrite <- entryCount c n e me in positive))

-- The histogram's values are the counts of its keys.
theorem valuesAreCounts (c: Circuits) (n: Nat): c.sizes n = List.map (Map.keys (labelCounts c n)) (labelCount c n) :=
  rewrite List.mapMap (Map.toList (labelCounts c n)) (labelCount c n) Pair.fst in
    List.mapCongMem (Map.toList (labelCounts c n)) Pair.snd (e => labelCount c n e.fst) (entryCount c n)

-- The spec's first boxes -----------------------------------------------------

-- No lower box has b's label: the spec counts b's circuit at b.
def firstBox (c: Circuits) (b: Nat): Bool := !(List.range b |> .any (other => c.labelOf other == c.labelOf b))

-- The labels of the first boxes don't repeat ...
theorem firstsDistinct (c: Circuits): (k: Nat) -> (s: Nat) -> List.Distinct (List.map (List.filter (List.rangeFrom k s) (firstBox c)) c.labelOf)
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
                        (omega [List.memRangeFrom b k (Succ s) inRange]) (rewrite same, eqSelf (c.labelOf s) in rfl)
                    Bool.falseNotTrue (rewrite lower at first)))
          (firstsDistinct c k (Succ s))
      | False => firstsDistinct c k (Succ s)

-- ... and they are all the labels: each box's label is a first box's.
theorem firstOf (c: Circuits) (n: Nat): (fuel: Nat) -> (b: Nat) -> b < fuel -> b < n ->
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
            rewrite <- eqTrue (c.labelOf other) (c.labelOf b) same in firstOf c n fuel other omega omega)

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
    permMap (labelCount c n) (Map.keys (labelCounts c n)) (List.map (List.filter (List.range n) (firstBox c)) c.labelOf)
      (permOfSameMembers (Map.keys (labelCounts c n)) (List.map (List.filter (List.range n) (firstBox c)) c.labelOf)
        (keysDistinct _ None (Map.toList (labelCounts c n)) (Map.toListSorted (labelCounts c n)))
        (firstsDistinct c n 0)
        (label m => firstOfLabel c n label (labelOfKey c n label m))
        (label m => keyOfLabel c n label (labelOfFirst c n label m)))
