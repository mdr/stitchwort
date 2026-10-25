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
theorem sortedLargestFirst (xs: List Nat): List.Sorted atLeast (List.sortBy (a b => Nat.compare b a) xs) :=
  List.sortedCong (a b => Ordering.isLessEq (Nat.compare b a)) atLeast (a b => Nat.compareLeq b a) (List.sortBy (a b => Nat.compare b a) xs)
    (List.sortBySorted (a b => Nat.compare b a) (a b h => rewrite Nat.compareLeq a b in rewrite Nat.compareLeq b a at h in omega) xs)

-- The three largest of the same sizes in any order.
theorem threeLargestPerm (xs: List Nat) (ys: List Nat) (p: List.Perm xs ys): threeLargestProduct xs = threeLargestProduct ys :=
  let sortX := List.sortBy (a b => Nat.compare b a) xs
  let sortY := List.sortBy (a b => Nat.compare b a) ys
  Eq.cong (sorted => List.product (List.take 3 sorted))
    (sortedDescUnique sortX sortY (sortedLargestFirst xs) (sortedLargestFirst ys)
      (List.permTrans sortX xs sortY (List.sortByPerm _ xs) (List.permTrans xs ys sortY p (List.permSym sortY ys (List.sortByPerm _ ys)))))

-- Lists without repeats with the same members ------------------------------

theorem occurrencesMap (q: b -> Bool) (f: a -> b): (xs: List a) -> List.occurrences q (List.map f xs) = List.occurrences (x => q (f x)) xs
  | Nil => rfl
  | Cons x xs => rewrite occurrencesMap q f xs in rfl

theorem permMap (f: a -> b) (xs: List a) (ys: List a) (p: List.Perm xs ys): List.Perm (List.map f xs) (List.map f ys) :=
  q => rewrite occurrencesMap q f xs, occurrencesMap q f ys in p (x => q (f x))

theorem occurrencesFilter (q: a -> Bool) (r: a -> Bool): (xs: List a) -> List.occurrences q (List.filter r xs) = List.occurrences (x => q x && r x) xs
  | Nil => rfl
  | Cons x xs =>
    match e: r x with
      | True => rewrite occurrencesFilter q r xs, Bool.andTrue (q x) in rfl
      | False => rewrite occurrencesFilter q r xs, Bool.andFalse (q x) in rfl

theorem distinctFilter (r: a -> Bool): (xs: List a) -> List.Distinct xs -> List.Distinct (List.filter r xs)
  | Nil, d => Trivial
  | Cons x xs, Both notMem d =>
    match e: r x with
      | True => Both (m => notMem (And.left (List.memFilter r x xs m))) (distinctFilter r xs d)
      | False => distinctFilter r xs d

-- Counting q at x in a list without x ...
theorem occurrencesAbsent (q: Nat -> Bool) (x: Nat): (ys: List Nat) -> Not (List.Mem x ys) -> List.occurrences (z => q z && (z == x)) ys = 0
  | Nil, n => rfl
  | Cons y ys, n =>
    match e: y == x with
      | True => Void.exfalso (n (Inl (eqTrue y x e)))
      | False => rewrite Bool.andFalse (q y), occurrencesAbsent q x ys (m => n (Inr m)) in rfl

-- ... and in a list with x once.
theorem occurrencesOnce (q: Nat -> Bool) (x: Nat): (ys: List Nat) -> List.Distinct ys -> List.Mem x ys ->
    List.occurrences (z => q z && (z == x)) ys = Bool.toNat (q x)
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
    let others := List.filter (z => !(z == x)) ys
    let rest: List.occurrences q xs = List.occurrences q others :=
      permOfSameMembers xs others dx (distinctFilter (z => !(z == x)) ys dy)
        (z m =>
          List.memFilterIntro (z => !(z == x)) z ys (there z (Inr m))
            (match e: z == x with
              | True => Void.exfalso (notMem (rewrite <- eqTrue z x e in m))
              | False => rfl))
        (z m =>
          match List.memFilter (z => !(z == x)) z ys m with
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
    List.Mem key (List.map Pair.fst xs) -> Map.Tree.Above ord lo key
  | lo, Nil, asc, m => Void.exfalso m
  | lo, Cons (kk, vv) rest, Both above arest, Inl e => rewrite <- e in above
  | None, Cons (kk, vv) rest, Both above arest, Inr m => Trivial
  | Some low, Cons (kk, vv) rest, Both above arest, Inr m => ord.trans low kk key above (keysAbove ord key (Some kk) rest arest m)

-- ... so the keys don't repeat.
theorem keysDistinct (ord: Ord k): (lo: Option k) -> (xs: List (k, v)) -> Map.Spec.Ascending ord lo xs -> List.Distinct (List.map Pair.fst xs)
  | lo, Nil, asc => Trivial
  | lo, Cons (kk, vv) rest, Both above arest =>
    Both (m => Ordering.lessNotEqual (Eq.trans (Eq.sym (keysAbove ord kk (Some kk) rest arest m)) (Ord.compareSelf kk)))
      (keysDistinct ord (Some kk) rest arest)

-- No count is 0.
theorem countsPositive (key: Nat): (xs: List Nat) -> (m: Map Nat Nat) -> ((v: Nat) -> Map.get key m = Some v -> 0 < v) ->
    (v: Nat) -> Map.get key (List.foldLeft (acc x => Map.insertWith Nat.add x 1 acc) m xs) = Some v -> 0 < v
  | Nil, m, h, v, found => h v found
  | Cons x rest, m, h, v, found =>
    countsPositive key rest (Map.insertWith Nat.add x 1 m) (v g =>
      match e: key == x with
        | True =>
          let inserted := rewrite eqTrue key x e, Map.getInsertWith Nat.add x 1 m at g
          match c: Map.get x m with
            | None => rewrite <- Option.someInjective _ v inserted in rfl
            | Some old => rewrite <- Option.someInjective _ v inserted in omega
        | False => h v (rewrite Map.getInsertWithOther Nat.add x 1 key (DecEq.soundFalse key x e) m at g))
      v found

-- How many of the boxes 0 to n - 1 have the label.
def labelCount (c: Circuits) (n: Nat) (label: Nat): Nat := List.count (x => x == label) (List.map c.labelOf (List.range n))

-- The histogram of the labels.
def labelCounts (c: Circuits) (n: Nat): Map Nat Nat := Map.counts (List.map c.labelOf (List.range n))

theorem getOrLabelCounts (c: Circuits) (n: Nat) (label: Nat): Map.getOr 0 label (labelCounts c n) = labelCount c n label :=
  rewrite Map.getOrCounts label (List.map c.labelOf (List.range n)), Map.Spec.sameKeyDecide label _ in rfl

-- Each entry of the histogram is a label and its count.
theorem entryCount (c: Circuits) (n: Nat): (e: (Nat, Nat)) -> List.Mem e (Map.toList (labelCounts c n)) -> e.snd = labelCount c n e.fst
  | (label, v), m =>
    Eq.trans (Eq.sym (Eq.cong (Option.getOrElse 0) ((Map.memToList label v (labelCounts c n)).forward m))) (getOrLabelCounts c n label)

-- A label is counted once at least exactly when some box has it.
theorem memOfCount (c: Circuits) (n: Nat) (label: Nat) (h: 0 < labelCount c n label): List.Mem label (List.map c.labelOf (List.range n)) :=
  List.anyTrueElim (x => x == label) (List.Mem label (List.map c.labelOf (List.range n))) (List.map c.labelOf (List.range n))
    (rewrite List.anyOccurrences (x => x == label) (List.map c.labelOf (List.range n)), <- List.countOccurrences (x => x == label) _ in h)
    (x m e => rewrite <- eqTrue x label e in m)

theorem countOfMem (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (List.map c.labelOf (List.range n))): 0 < labelCount c n label :=
  rewrite List.countOccurrences (x => x == label) _, <- List.anyOccurrences (x => x == label) _ in
    List.anyOfMem (x => x == label) label (eqSelf label) (List.map c.labelOf (List.range n)) m

-- The histogram's keys are the labels.
theorem keyOfLabel (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (List.map c.labelOf (List.range n))):
    List.Mem label (Map.keys (labelCounts c n)) :=
  let positive: 0 < Map.getOr 0 label (labelCounts c n) := rewrite getOrLabelCounts c n label in countOfMem c n label m
  match g: Map.get label (labelCounts c n) with
    | None => Void.exfalso (Bool.falseNotTrue positive)
    | Some v => List.memMap Pair.fst (label, v) (Map.toList (labelCounts c n)) ((Map.memToList label v (labelCounts c n)).backward g)

theorem labelOfKey (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (Map.keys (labelCounts c n))):
    List.Mem label (List.map c.labelOf (List.range n)) :=
  List.anyElim ((e: (Nat, Nat)) => e.fst = label) (List.Mem label (List.map c.labelOf (List.range n))) (Map.toList (labelCounts c n))
    (List.memMapAny Pair.fst label (Map.toList (labelCounts c n)) m)
    (e me key =>
      let positive: 0 < e.snd :=
        match e with
          | (k, v) =>
            countsPositive k (List.map c.labelOf (List.range n)) Map.empty (v g => Void.exfalso (Option.noneNotSome v g)) v
              ((Map.memToList k v (labelCounts c n)).forward me)
      rewrite <- key in memOfCount c n e.fst (rewrite <- entryCount c n e me in positive))

-- The histogram's values are the counts of its keys.
theorem valuesAreCounts (c: Circuits) (n: Nat): c.sizes n = List.map (labelCount c n) (Map.keys (labelCounts c n)) :=
  rewrite List.mapMap (labelCount c n) Pair.fst (Map.toList (labelCounts c n)) in
    List.mapCongMem Pair.snd (e => labelCount c n e.fst) (Map.toList (labelCounts c n)) (entryCount c n)

-- The spec's first boxes -----------------------------------------------------

-- No lower box has b's label: the spec counts b's circuit at b.
def firstBox (c: Circuits) (b: Nat): Bool := !(List.range b |> .any (other => c.labelOf other == c.labelOf b))

-- The labels of the first boxes don't repeat ...
theorem firstsDistinct (c: Circuits): (k: Nat) -> (s: Nat) -> List.Distinct (List.map c.labelOf (List.filter (firstBox c) (List.rangeFrom k s)))
  | Zero, s => Trivial
  | Succ k, s =>
    match e: firstBox c s with
      | True =>
        Both
          (m =>
            List.anyElim (b => c.labelOf b = c.labelOf s) Void (List.filter (firstBox c) (List.rangeFrom k (Succ s)))
              (List.memMapAny c.labelOf (c.labelOf s) _ m)
              (b mb same =>
                match List.memFilter (firstBox c) b (List.rangeFrom k (Succ s)) mb with
                  | Both inRange first =>
                    let lower: List.any (other => c.labelOf other == c.labelOf b) (List.range b) = True :=
                      List.anyRangeIntro (other => c.labelOf other == c.labelOf b) b 0 s omega
                        (omega [List.memRangeFrom b k (Succ s) inRange]) (rewrite same, eqSelf (c.labelOf s) in rfl)
                    Bool.falseNotTrue (rewrite lower at first)))
          (firstsDistinct c k (Succ s))
      | False => firstsDistinct c k (Succ s)

-- ... and they are all the labels: each box's label is a first box's.
theorem firstOf (c: Circuits) (n: Nat): (fuel: Nat) -> (b: Nat) -> b < fuel -> b < n ->
    List.Mem (c.labelOf b) (List.map c.labelOf (List.filter (firstBox c) (List.range n)))
  | Zero, b, h, hb => Void.exfalso (Bool.falseNotTrue h)
  | Succ fuel, b, h, hb =>
    match g: List.any (other => c.labelOf other == c.labelOf b) (List.range b) with
      | False =>
        List.memMap c.labelOf b _ (List.memFilterIntro (firstBox c) b (List.range n) (List.memRangeFromIntro b n 0 omega hb) (rewrite g in rfl))
      | True =>
        List.anyTrueElim (other => c.labelOf other == c.labelOf b) (List.Mem (c.labelOf b) (List.map c.labelOf (List.filter (firstBox c) (List.range n))))
          (List.range b) g
          (other mo same =>
            let below := List.memRangeFrom other b 0 mo
            rewrite <- eqTrue (c.labelOf other) (c.labelOf b) same in firstOf c n fuel other omega omega)

theorem labelOfFirst (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (List.map c.labelOf (List.filter (firstBox c) (List.range n)))):
    List.Mem label (List.map c.labelOf (List.range n)) :=
  List.anyElim (b => c.labelOf b = label) (List.Mem label (List.map c.labelOf (List.range n))) (List.filter (firstBox c) (List.range n))
    (List.memMapAny c.labelOf label _ m)
    (b mb e => rewrite <- e in List.memMap c.labelOf b (List.range n) (And.left (List.memFilter (firstBox c) b (List.range n) mb)))

theorem firstOfLabel (c: Circuits) (n: Nat) (label: Nat) (m: List.Mem label (List.map c.labelOf (List.range n))):
    List.Mem label (List.map c.labelOf (List.filter (firstBox c) (List.range n))) :=
  List.anyElim (b => c.labelOf b = label) (List.Mem label (List.map c.labelOf (List.filter (firstBox c) (List.range n)))) (List.range n)
    (List.memMapAny c.labelOf label _ m)
    (b mb e => rewrite <- e in firstOf c n (Succ b) b omega (And.right (List.memRangeFrom b n 0 mb)))

-- The spec's sizes, with "same label" as the test, are the counts of the
-- first boxes' labels.
theorem circuitSizesAreCounts (c: Circuits) (n: Nat):
    circuitSizes n (a b => c.labelOf a == c.labelOf b) = List.map (labelCount c n) (List.map c.labelOf (List.filter (firstBox c) (List.range n))) :=
  rewrite List.mapMap (labelCount c n) c.labelOf _, List.countMap (x => x == c.labelOf _) c.labelOf (List.range n) in rfl

-- The program's sizes are the spec's, in another order.
theorem sizesPerm (c: Circuits) (n: Nat): List.Perm (c.sizes n) (circuitSizes n (a b => c.labelOf a == c.labelOf b)) :=
  rewrite valuesAreCounts c n, circuitSizesAreCounts c n in
    permMap (labelCount c n) (Map.keys (labelCounts c n)) (List.map c.labelOf (List.filter (firstBox c) (List.range n)))
      (permOfSameMembers (Map.keys (labelCounts c n)) (List.map c.labelOf (List.filter (firstBox c) (List.range n)))
        (keysDistinct _ None (Map.toList (labelCounts c n)) (Map.toListSorted (labelCounts c n)))
        (firstsDistinct c n 0)
        (label m => firstOfLabel c n label (labelOfKey c n label m))
        (label m => keyOfLabel c n label (labelOfFirst c n label m)))
