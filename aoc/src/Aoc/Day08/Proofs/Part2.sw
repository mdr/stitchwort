-- Day 8, part 2, proved for every list of boxes (`part2Correct`): if
-- connection k is the last one needed to put all the boxes in one circuit,
-- the program's answer is the product of the X coordinates of its two
-- boxes. With two or more boxes there always is such a connection
-- (`lastNeededExists`, at the bottom); with fewer there is no answer
-- (`part2NoBoxesToJoin`). The argument:
--   1. The count is the number of circuits: it is the number of boxes that
--      are their own label (`Counted`), since every label is a box labelled
--      with itself, and joining two circuits takes one such box away.
--   2. So the count is 1 exactly when all the boxes are in one circuit
--      (`countOneOf`, `oneCircuitOfCount`), by the label theorem.
--   3. `lastJoin` walks the connections in order and stops at the first
--      after which the count is 1 (`lastJoinFinds`): before connection k
--      the boxes weren't all in one circuit, after it they are.
--   4. All the connections together join every pair of boxes, so the first
--      k after which there is one circuit exists (`Nat.firstFrom`), and
--      connection k - 1 is the last needed.

namespace Aoc.Day08.Proofs
import Aoc.Day08 (..)
import Aoc.Day08.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Map, Nat, Option, Ord, Ordering, Pair, Void)

-- Counting --------------------------------------------------------------------

-- Exactly one of the numbers below n passes q.
theorem countOne (q: Nat → Bool) (n: Nat) (v: Nat) (hv: q v = True) (vn: v < n) (uniq: (b: Nat) → q b = True → b = v):
    List.occurrences (List.range n) q = 1 :=
  rewrite List.occurrencesSumBy (List.range n) q, <- Nat.keepIfOne _ in List.sumRangeOne q (b => 1) v hv uniq n 0 omega vn

-- If v (below n) passes p, the numbers below n passing p are those other
-- than v, and v.
theorem countWithout (p: Nat → Bool) (n: Nat) (v: Nat) (hv: p v = True) (vn: v < n):
    List.occurrences (List.range n) p = List.occurrences (List.range n) (b => p b ∧ ¬(b == v)) + 1 :=
  rewrite List.occurrencesSplit (List.range n) v p,
    countOne (b => p b ∧ (b == v)) n v (rewrite hv, DecEq.refl v in rfl) vn
      (b h => match e: b == v with
        | True => DecEq.sound b v e
        | False => Void.exfalso (Bool.falseNotTrue (rewrite Bool.andFalse (p b) at h)))
    in rfl

-- Two numbers below n that pass p, when only one does, are the same.
theorem onlyOne (p: Nat → Bool) (n: Nat) (one: List.occurrences (List.range n) p = 1) (x: Nat) (y: Nat)
    (hx: p x = True) (xn: x < n) (hy: p y = True) (yn: y < n): y = x :=
  match e: y == x with
    | True => DecEq.sound y x e
    | False =>
      let some: Nat.leq 1 (List.occurrences (List.range n) (b => p b ∧ ¬(b == x))) = True :=
        rewrite <- List.anyOccurrences (List.range n) (b => p b ∧ ¬(b == x)) in
          List.anyRangeIntro (b => p b ∧ ¬(b == x)) n 0 y omega yn (rewrite hy, e in rfl)
      omega [countWithout p n x hx xn]

-- The count is the number of circuits -----------------------------------------

-- The boxes 0 to n - 1 that are their own label.
def ownLabels (c: Circuits) (n: Nat): Nat := List.occurrences (List.range n) (b => c.labelOf b == b)

-- What the count of `circuits` says (point 1 at the top): labels are boxes,
-- labelled with themselves, and the count is how many there are.
type Counted (n: Nat) (circuits: Circuits): Prop = {
  counts: circuits.count = ownLabels circuits n,
  labelBelow: (b: Nat) → b < n → circuits.labelOf b < n,
  labelOwn: (b: Nat) → b < n → circuits.labelOf (circuits.labelOf b) = circuits.labelOf b
}

theorem countedAtStart (n: Nat): Counted n (Circuits.separate n) :=
  {
    counts = rewrite labelAtStart n _, DecEq.refl [a := Nat] _, List.occurrencesTrue (List.range n), List.lengthRangeFrom n 0 in rfl,
    labelBelow = b h => rewrite labelAtStart n b h in h,
    labelOwn = b h => rewrite labelAtStart n b h, labelAtStart n b h in rfl
  }

-- After the move, a box is its own label when it was and isn't f's old label.
theorem ownAfterMove (c: Circuits) (f: Nat) (s: Nat) (n: Nat) (counted: Counted n c) (hs: s < n)
    (differ: (c.labelOf f == c.labelOf s) = False) (b: Nat):
    (relabel (c.labelOf f) (c.labelOf s) (c.labelOf b) == b) = ((c.labelOf b == b) ∧ ¬(b == c.labelOf f)) :=
  match g: c.labelOf b == c.labelOf f with
    | True =>
      let lf := DecEq.sound (c.labelOf b) (c.labelOf f) g
      match h2: c.labelOf s == b with
        | True =>
          -- b would be s's label, so its own label: then f's label is s's.
          let bs := DecEq.sound (c.labelOf s) b h2
          Void.exfalso (DecEq.soundFalse (c.labelOf f) (c.labelOf s) differ
            (Eq.trans (Eq.sym lf) (rewrite <- bs, counted.labelOwn s hs in rfl)))
        | False =>
          rewrite lf in
            match h3: b == c.labelOf f with
              | True => rewrite Bool.andFalse (c.labelOf f == b) in rfl
              | False => rewrite DecEq.eqComm (c.labelOf f) b, h3 in rfl
    | False =>
      match h2: c.labelOf b == b with
        | True => rewrite <- DecEq.sound (c.labelOf b) b h2, g in rfl
        | False => rfl

theorem countedMoved (n: Nat) (done: List (Nat, Nat)) (c: Circuits) (f: Nat) (s: Nat) (hf: f < n) (hs: s < n)
    (differ: (c.labelOf f == c.labelOf s) = False) (inv: Labelled n done c) (counted: Counted n c): Counted n (moved c f s) :=
  let after: (b: Nat) → b < n → (moved c f s).labelOf b = relabel (c.labelOf f) (c.labelOf s) (c.labelOf b) := movedLabel c f s n inv.stored
  let below: (b: Nat) → b < n → relabel (c.labelOf f) (c.labelOf s) (c.labelOf b) < n :=
    b h => match g: c.labelOf b == c.labelOf f with
      | True => counted.labelBelow s hs
      | False => counted.labelBelow b h
  {
    counts =
      calc (moved c f s).count
        _ = ownLabels c n - 1 := rewrite counted.counts in rfl
        _ = List.occurrences (List.range n) (b => c.labelOf b == b ∧ ¬(b == c.labelOf f)) :=
          rewrite countWithout (b => c.labelOf b == b) n (c.labelOf f) (rewrite counted.labelOwn f hf in DecEq.refl (c.labelOf f)) (counted.labelBelow f hf)
            in omega
        _ = ownLabels (moved c f s) n :=
          rewrite after _, ownAfterMove c f s n counted hs differ _ in rfl,
    labelBelow = b h => rewrite after b h in below b h,
    labelOwn = b h =>
      rewrite after b h, after (relabel (c.labelOf f) (c.labelOf s) (c.labelOf b)) (below b h) in
        match g: c.labelOf b == c.labelOf f with
          | True => rewrite counted.labelOwn s hs in relabelTo (c.labelOf f) (c.labelOf s) differ
          | False => rewrite counted.labelOwn b h, g in rfl
  }

theorem countedJoin (n: Nat) (done: List (Nat, Nat)) (c: Circuits) (f: Nat) (s: Nat) (hf: f < n) (hs: s < n)
    (inv: Labelled n done c) (counted: Counted n c): Counted n (c.join f s) :=
  match e: c.labelOf f == c.labelOf s with
    | True => counted
    | False => countedMoved n done c f s hf hs e inv counted

-- The count is 1 exactly when all the boxes are in one circuit -------------

theorem oneCircuitMore (n: Nat) (xs: List (Nat, Nat)) (ys: List (Nat, Nat)) (more: (e: (Nat, Nat)) → List.Mem e xs → List.Mem e ys)
    (one: OneCircuit n xs): OneCircuit n ys :=
  a b ha hb => joinedMore xs ys more a b (one a b ha hb)

-- With all the boxes in one circuit, the one box that is its own label is
-- box 0's label.
theorem countOneOf (n: Nat) (done: List (Nat, Nat)) (c: Circuits) (inv: Labelled n done c) (counted: Counted n c)
    (some: 0 < n) (one: OneCircuit n done): c.count = 1 :=
  let r := c.labelOf 0
  let same: (b: Nat) → b < n → c.labelOf b = r :=
    b h => DecEq.sound (c.labelOf b) r ((labelsTellOf n done c inv b 0 h some).backward (one b 0 h some))
  rewrite counted.counts, same _ in countOne (b => r == b) n r (DecEq.refl r) (counted.labelBelow 0 some) (b h => Eq.sym (DecEq.sound r b h))

-- With one box its own label, every box has that label, so all are joined.
theorem oneCircuitOfCount (n: Nat) (done: List (Nat, Nat)) (c: Circuits) (inv: Labelled n done c) (counted: Counted n c)
    (one: c.count = 1): OneCircuit n done :=
  a b ha hb =>
    let own := Eq.trans (Eq.sym counted.counts) one
    let same: c.labelOf b = c.labelOf a :=
      onlyOne (b => c.labelOf b == b) n own (c.labelOf a) (c.labelOf b)
        (rewrite counted.labelOwn a ha in DecEq.refl (c.labelOf a)) (counted.labelBelow a ha)
        (rewrite counted.labelOwn b hb in DecEq.refl (c.labelOf b)) (counted.labelBelow b hb)
    (labelsTellOf n done c inv a b ha hb).forward (rewrite same in DecEq.refl (c.labelOf a))

-- No boxes are always in one circuit.
theorem oneCircuitOfNone (done: List (Nat, Nat)): OneCircuit 0 done := a b ha hb => Void.exfalso (Bool.falseNotTrue ha)

-- When not all boxes are in one circuit, the count is above 1.
theorem countAboveOne (n: Nat) (done: List (Nat, Nat)) (c: Circuits) (inv: Labelled n done c) (counted: Counted n c)
    (notOne: Not (OneCircuit n done)): (c.count > 1) = True :=
  match n with
    | Zero => Void.exfalso (notOne (oneCircuitOfNone done))
    | Succ m =>
      let atLeastOne: Nat.leq 1 c.count = True :=
        rewrite counted.counts, <- List.anyOccurrences (List.range (Succ m)) (b => c.labelOf b == b) in
          List.anyRangeIntro (b => c.labelOf b == b) (Succ m) 0 (c.labelOf 0) omega (counted.labelBelow 0 rfl)
            (rewrite counted.labelOwn 0 rfl in DecEq.refl (c.labelOf 0))
      match e: c.count with
        | Zero => Void.exfalso (Bool.falseNotTrue atLeastOne)
        | Succ Zero => Void.exfalso (notOne (oneCircuitOfCount (Succ m) done c inv counted e))
        | Succ (Succ k) => rfl

-- When not all boxes are in one circuit, the count isn't 1.
theorem countNotOne (n: Nat) (done: List (Nat, Nat)) (c: Circuits) (inv: Labelled n done c) (counted: Counted n c)
    (notOne: Not (OneCircuit n done)): (c.count == 1) = False :=
  match e: c.count == 1 with
    | True => Void.exfalso (notOne (oneCircuitOfCount n done c inv counted (DecEq.sound c.count 1 e)))
    | False => rfl

-- Part 2 ------------------------------------------------------------------------

-- Walking the connections `ps` after `done`: if connection k of `ps` is the
-- last needed, `lastJoin` stops there.
theorem lastJoinFinds (points: List Point): (ps: List (Nat, Nat)) → (k: Nat) → (done: List (Nat, Nat)) → (c: Circuits) →
    Labelled points.length done c → Counted points.length c → List.all ps (boxesBelow points.length) = True →
    OneCircuit points.length (List.append done (List.take ps (Succ k))) → Not (OneCircuit points.length (List.append done (List.take ps k))) →
    lastJoin c (List.map ps (connectionKey points)) = Some ((List.getOr ps (0, 0) k).fst, (List.getOr ps (0, 0) k).snd)
  | Nil, Zero, done, c, inv, counted, ok, after, before => Void.exfalso (before after)
  | Nil, Succ k, done, c, inv, counted, ok, after, before => Void.exfalso (before after)
  | Cons (f, s) ps, k, done, c, inv, counted, ok, after, before =>
    let n := points.length
    match r: boxesBelow n (f, s) with
      | False => Void.exfalso (Bool.falseNotTrue ok)
      | True =>
        let hf: f < n := Bool.andLeft _ _ r
        let hs: s < n := Bool.andRight _ _ r
        let inv2 := labelledJoin n done c f s hf hs inv
        let counted2 := countedJoin n done c f s hf hs inv counted
        match k with
          | Zero =>
            -- Connection 0 of `ps`: before it, more than one circuit; after it, one.
            let notYet: Not (OneCircuit n done) := one => before (rewrite List.appendNil done in one)
            let some: 0 < n := match n with | Zero => Void.exfalso (notYet (oneCircuitOfNone done)) | Succ m => rfl
            rewrite countAboveOne n done c inv counted notYet, countOneOf n (List.append done [(f, s)]) (c.join f s) inv2 counted2 some after
              in rfl
          | Succ k =>
            -- A later connection: after this one, not yet one circuit.
            let moreAfter: (e: (Nat, Nat)) → List.Mem e (List.append done [(f, s)]) → List.Mem e (List.append done (Cons (f, s) (List.take ps k))) :=
              e m => rewrite <- List.appendAssoc done [(f, s)] (List.take ps k) in List.anyAppendLeft (y => y = e) (List.append done [(f, s)]) (List.take ps k) m
            let notYet: Not (OneCircuit n (List.append done [(f, s)])) := one => before (oneCircuitMore n _ _ moreAfter one)
            rewrite countNotOne n (List.append done [(f, s)]) (c.join f s) inv2 counted2 notYet, Bool.andFalse (c.count > 1) in
              lastJoinFinds points ps k (List.append done [(f, s)]) (c.join f s) inv2 counted2 ok
                (rewrite List.appendAssoc done [(f, s)] (List.take ps (Succ k)) in after)
                (rewrite List.appendAssoc done [(f, s)] (List.take ps k) in before)

theorem allOrderInRange (points: List Point): List.all (connectionOrder points) (boxesBelow points.length) = True :=
  rewrite List.allPerm (connectionOrder points) (allPairs points.length) (List.sortOnPerm (allPairs points.length) (connectionKey points))
      (boxesBelow points.length)
    in allPairsBoth (i => Nat.leq (Succ i) points.length) (List.range points.length)
      (List.allRangeIntro (i => Nat.leq (Succ i) points.length) points.length 0 (i lo hi => hi))

-- Part 2 is right: for every list of boxes, if connection k is the last one
-- needed to put all the boxes in one circuit, the program's answer is the
-- product of the X coordinates of its two boxes.
theorem part2Correct (points: List Point) (k: Nat) (last: LastNeeded points k):
    solvePart2 (Boxes.of points) = Some (xProduct points (connectionAt points k)) :=
  rewrite closestFirstIsOrder points,
    lastJoinFinds points (connectionOrder points) k Nil (Circuits.separate points.length)
      (labelledAtStart points.length) (countedAtStart points.length) (allOrderInRange points) (And.left last) (And.right last)
    in rfl

-- With fewer than two boxes, they start in one circuit and there is no answer.
theorem part2NoBoxesToJoin: (points: List Point) → points.length ≤ 1 → solvePart2 (Boxes.of points) = None
  | Nil, h => rfl
  | Cons p Nil, h => rfl
  | Cons p (Cons q qs), h => Void.exfalso (Bool.falseNotTrue h)

-- Some connection is the last needed -----------------------------------------

-- Every pair a < b of the numbers from s on is a pair of them.
theorem memPairs (a: Nat) (b: Nat) (ab: a < b): (c: Nat) → (s: Nat) → s ≤ a → b < s + c → List.Mem (a, b) (List.pairs (List.rangeFrom c s))
  | Zero, s, h1, h2 => omega
  | Succ c, s, h1, h2 =>
    let h3: b < Succ s + c := omega
    match e: Nat.equal s a with
      | True =>
        rewrite <- Nat.equalSound s a e in
          List.anyAppendLeft (y => y = (s, b)) (List.map (List.rangeFrom c (Succ s)) (y => (s, y))) (List.pairs (List.rangeFrom c (Succ s)))
            (List.memMap (List.rangeFrom c (Succ s)) b (List.memRangeFromIntro b c (Succ s) (rewrite Nat.equalSound s a e in ab) h3) (y => (s, y)))
      | False =>
        List.anyAppendRight (y => y = (a, b)) (List.map (List.rangeFrom c (Succ s)) (y => (s, y))) (List.pairs (List.rangeFrom c (Succ s)))
          (memPairs a b ab c (Succ s) omega h3)

-- Every pair of boxes is one of the connections.
theorem memOrder (points: List Point) (a: Nat) (b: Nat) (ab: a < b) (bn: b < points.length): List.Mem (a, b) (connectionOrder points) :=
  List.memPerm (allPairs points.length) (connectionOrder points)
    (List.permSym _ _ (List.sortOnPerm (allPairs points.length) (connectionKey points)))
    (a, b) (memPairs a b ab points.length 0 omega bn)

-- All the connections put all the boxes in one circuit.
theorem allConnectionsJoinAll (points: List Point): OneCircuit points.length (connectionOrder points) :=
  a b ha hb =>
    match e: Nat.compare a b with
      | Less => Connected (memOrder points a b (Nat.lessOfCompare a b e) hb)
      | Equal => rewrite Nat.compareEqual a b e in Itself b
      | Greater => Backwards (Connected (memOrder points b a (Nat.lessOfCompare b a (rewrite e at Nat.compareFlip a b)) ha))

theorem countedJoinAll (n: Nat): (rest: List (Nat, Nat)) → (done: List (Nat, Nat)) → (c: Circuits) →
    List.all rest (boxesBelow n) = True → Labelled n done c → Counted n c → Counted n (joinAll c rest)
  | Nil, done, c, ok, inv, counted => counted
  | Cons (f, s) rest, done, c, ok, inv, counted =>
    match r: boxesBelow n (f, s) with
      | True =>
        countedJoinAll n rest (List.append done [(f, s)]) (c.join f s) ok
          (labelledJoin n done c f s (Bool.andLeft _ _ r) (Bool.andRight _ _ r) inv)
          (countedJoin n done c f s (Bool.andLeft _ _ r) (Bool.andRight _ _ r) inv counted)
      | False => Void.exfalso (Bool.falseNotTrue ok)

-- After the first j connections, is there one circuit?
def oneAfter (points: List Point) (j: Nat): Bool := (joinAll (Circuits.separate points.length) (firstConnections j points)).count == 1

theorem oneAfterTells (points: List Point) (j: Nat) (some: 0 < points.length):
    Iff (oneAfter points j = True) (OneCircuit points.length (firstConnections j points)) :=
  let n := points.length
  let ok := allTake (boxesBelow n) j (connectionOrder points) (allOrderInRange points)
  let inv := labelledJoinAll n (firstConnections j points) Nil (Circuits.separate n) ok (labelledAtStart n)
  let counted := countedJoinAll n (firstConnections j points) Nil (Circuits.separate n) ok (labelledAtStart n) (countedAtStart n)
  {
    forward = h => oneCircuitOfCount n (firstConnections j points) _ inv counted (DecEq.sound _ 1 h),
    backward = one => rewrite countOneOf n (firstConnections j points) _ inv counted some one in DecEq.refl 1
  }

-- With two or more boxes, some connection is the last one needed: the first
-- after which there is one circuit, as all of them make one.
theorem lastNeededExists (points: List Point) (two: 2 ≤ points.length): Exists Nat (LastNeeded points) :=
  let n := points.length
  let some: 0 < n := omega
  let total := (connectionOrder points).length
  let first := Nat.firstFrom (oneAfter points) (Succ total) 0
  let atEnd: oneAfter points total = True :=
    (oneAfterTells points total some).backward
      (rewrite List.takeAll (connectionOrder points) total omega in allConnectionsJoinAll points)
  let found: oneAfter points first = True :=
    Nat.firstFromFound (oneAfter points) (Succ total) 0 total omega omega atEnd
  let notAtStart: oneAfter points 0 = False :=
    match e: n == 1 with
      | True => Void.exfalso (Bool.falseNotTrue (rewrite DecEq.sound n 1 e at two))
      | False => rfl
  match g: first with
    | Zero => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym notAtStart) found))
    | Succ k =>
      Witness k (Both
        ((oneAfterTells points (Succ k) some).forward found)
        (one => Bool.falseNotTrue (Eq.trans (Eq.sym (Nat.firstFromBefore (oneAfter points) (Succ total) 0 k omega omega))((oneAfterTells points k some).backward one))))
