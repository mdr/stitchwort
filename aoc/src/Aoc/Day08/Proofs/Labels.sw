-- Day 8's circuit labels, proved: after joining any connections in order,
-- two boxes have the same label exactly when the connections join them
-- (`labelsTell`, at the bottom). Part1.sw and Part2.sw build on it.
--
-- The argument: four facts hold of the labels after every connection
-- (`Labelled`), from the start (`labelledAtStart`) and through each join
-- (`labelledJoin`):
--   1. every box has its label stored in the map;
--   2. the connections so far are between boxes that exist;
--   3. the two boxes of every connection so far have the same label;
--   4. every box is joined to its label (a label is one of the boxes of
--      its circuit).
-- From 3, joined boxes have the same label: each link of the chain keeps
-- it (`sameLabelOfJoined`). From 4, boxes with the same label are joined:
-- both are joined to the label. A join keeps 3 and 4 because the boxes
-- labelled like the first box are exactly its circuit, and they all move to
-- the second box's circuit, which the new connection joins it to.

namespace Aoc.Day08.Proofs
import Aoc.Day08 (..)
import Aoc.Day08.Spec (..)
import Std (And, Bool, DecEq, Eq, List, Map, Nat, Option, Ord, Ordering, Pair, Void)

-- Joining the connections in order, from the circuits given: `solvePart1`'s fold.
def joinAll (circuits: Circuits) (connections: List (Nat, Nat)): Circuits :=
  connections.foldLeft circuits (c pair => c.join pair.fst pair.snd)

-- Both boxes of the pair are among the boxes 0 to n - 1.
def boxesBelow (n: Nat) (pair: (Nat, Nat)): Bool := Nat.leq (Succ pair.fst) n ∧ Nat.leq (Succ pair.snd) n

-- Facts about `Joined` -------------------------------------------------------

-- More connections join at least the same boxes.
theorem joinedMore (xs: List (Nat, Nat)) (ys: List (Nat, Nat)) (more: (e: (Nat, Nat)) → List.Mem e xs → List.Mem e ys):
    (a: Nat) → (b: Nat) → Joined xs a b → Joined ys a b
  | a, a, Itself a => Itself a
  | a, b, Connected m => Connected (more (a, b) m)
  | a, b, Backwards j => Backwards (joinedMore xs ys more b a j)
  | a, c, Chain [b := m] j k => Chain (joinedMore xs ys more a m j) (joinedMore xs ys more m c k)

-- ... in particular, connections added at the end.
theorem joinedAppend (xs: List (Nat, Nat)) (extra: List (Nat, Nat)) (a: Nat) (b: Nat) (j: Joined xs a b): Joined (List.append xs extra) a b :=
  joinedMore xs (List.append xs extra) (e m => List.anyAppendLeft (y => y = e) xs extra m) a b j

-- If the two boxes of every connection have the same label, so do any two
-- joined boxes: each link of the chain keeps the label.
theorem sameLabelOfJoined (label: Nat → Nat) (xs: List (Nat, Nat)) (agree: (a: Nat) → (b: Nat) → List.Mem (a, b) xs → label a = label b):
    (a: Nat) → (b: Nat) → Joined xs a b → label a = label b
  | a, a, Itself a => rfl
  | a, b, Connected m => agree a b m
  | a, b, Backwards j => Eq.sym (sameLabelOfJoined label xs agree b a j)
  | a, c, Chain [b := m] j k => Eq.trans (sameLabelOfJoined label xs agree a m j) (sameLabelOfJoined label xs agree m c k)

-- The connection just added.
theorem memLast (e: (Nat, Nat)) (xs: List (Nat, Nat)): List.Mem e (List.append xs [e]) := List.anyAppendRight (y => y = e) xs [e] (Inl rfl)

-- A connection of `xs` then `e` is one of `xs`, or `e`.
theorem memSnoc (a: Nat) (b: Nat) (e: (Nat, Nat)) (xs: List (Nat, Nat)) (m: List.Mem (a, b) (List.append xs [e])) (goal: Prop)
    (old: List.Mem (a, b) xs → goal) (new: And (a = e.fst) (b = e.snd) → goal): goal :=
  match List.memAppend (a, b) xs [e] m with
    | Inl o => old o
    | Inr (Inl h) => new (Both (Eq.sym (Eq.cong Pair.fst h)) (Eq.sym (Eq.cong Pair.snd h)))
    | Inr (Inr v) => Void.exfalso v

-- Labels ---------------------------------------------------------------------

-- What the labels of `circuits` say about the boxes 0 to n - 1 after the
-- connections `done` (the four facts at the top).
type Labelled (n: Nat) (done: List (Nat, Nat)) (circuits: Circuits): Prop = {
  stored: (b: Nat) → b < n → Map.get circuits.labels b = Some (circuits.labelOf b),
  inRange: (a: Nat) → (b: Nat) → List.Mem (a, b) done → And (a < n) (b < n),
  agree: (a: Nat) → (b: Nat) → List.Mem (a, b) done → circuits.labelOf a = circuits.labelOf b,
  labelJoined: (b: Nat) → b < n → Joined done b (circuits.labelOf b)
}

-- At the start each box is its own label ----------------------------------

-- The map built from (s, s), (s + 1, s + 1), ..., has nothing for a box below s ...
theorem lookupBelow (b: Nat): (c: Nat) → (s: Nat) → b < s →
    Map.lookupLast b (List.map (List.rangeFrom c s) (box => (box, box))) = None
  | Zero, s, h => rfl
  | Succ c, s, h =>
    rewrite lookupBelow b c (Succ s) omega in
      match e: Ord.compare b s with
        | Less => rfl
        | Equal => omega [Nat.compareEqual b s e]
        | Greater => rfl

-- ... and each box from s on is its own label.
theorem lookupRange (b: Nat): (c: Nat) → (s: Nat) → s ≤ b → b < s + c →
    Map.lookupLast b (List.map (List.rangeFrom c s) (box => (box, box))) = Some b
  | Zero, s, h1, h2 => omega
  | Succ c, s, h1, h2 =>
    match e: Nat.equal s b with
      | True =>
        rewrite <- Nat.equalSound s b e, lookupBelow s c (Succ s) omega, Ord.compareSelf s in rfl
      | False =>
        rewrite lookupRange b c (Succ s) omega omega in rfl

theorem storedAtStart (n: Nat) (b: Nat) (h: b < n): Map.get (Circuits.separate n).labels b = Some b :=
  rewrite Map.getFromList b (List.map (List.range n) (box => (box, box))) in lookupRange b n 0 omega h

theorem labelAtStart (n: Nat) (b: Nat) (h: b < n): (Circuits.separate n).labelOf b = b := rewrite storedAtStart n b h in rfl

theorem labelledAtStart (n: Nat): Labelled n Nil (Circuits.separate n) :=
  {
    stored = b h => rewrite storedAtStart n b h in rfl,
    inRange = a b m => Void.exfalso m,
    agree = a b m => Void.exfalso m,
    labelJoined = b h => rewrite labelAtStart n b h in Itself b
  }

-- A join keeps the four facts ------------------------------------------------

-- After joining two boxes with different labels, a box labelled like the
-- first takes the second's label, and the others keep theirs.
def relabel (from: Nat) (to: Nat) (label: Nat): Nat := if label == from then to else label

-- What `join` makes of two boxes with different labels.
def moved (c: Circuits) (f: Nat) (s: Nat): Circuits :=
  { labels = c.labels |> Map.map (relabel (c.labelOf f) (c.labelOf s)), count = c.count - 1 }

theorem joinSame (c: Circuits) (f: Nat) (s: Nat) (same: (c.labelOf f == c.labelOf s) = True): c.join f s = c :=
  rewrite same in rfl

theorem joinDiffers (c: Circuits) (f: Nat) (s: Nat) (differ: (c.labelOf f == c.labelOf s) = False): c.join f s = moved c f s :=
  rewrite differ in rfl

-- The new labels: the old ones, relabelled.
theorem movedStored (c: Circuits) (f: Nat) (s: Nat) (n: Nat) (stored: (b: Nat) → b < n → Map.get c.labels b = Some (c.labelOf b))
    (b: Nat) (h: b < n): Map.get (moved c f s).labels b = Some (relabel (c.labelOf f) (c.labelOf s) (c.labelOf b)) :=
  rewrite Map.getMap c.labels b (relabel (c.labelOf f) (c.labelOf s)), stored b h in rfl

theorem movedLabel (c: Circuits) (f: Nat) (s: Nat) (n: Nat) (stored: (b: Nat) → b < n → Map.get c.labels b = Some (c.labelOf b))
    (b: Nat) (h: b < n): (moved c f s).labelOf b = relabel (c.labelOf f) (c.labelOf s) (c.labelOf b) :=
  rewrite movedStored c f s n stored b h in rfl

-- s's label stays, f's moves to it.
theorem relabelTo (from: Nat) (to: Nat) (differ: (from == to) = False): relabel from to to = to :=
  match g: to == from with
    | True => Void.exfalso (DecEq.soundFalse from to differ (Eq.sym (DecEq.sound to from g)))
    | False => rfl

theorem relabelFrom (from: Nat) (to: Nat): relabel from to from = to := rewrite DecEq.refl from in rfl

theorem labelledMoved (n: Nat) (done: List (Nat, Nat)) (c: Circuits) (f: Nat) (s: Nat) (hf: f < n) (hs: s < n)
    (differ: (c.labelOf f == c.labelOf s) = False) (inv: Labelled n done c): Labelled n (List.append done [(f, s)]) (moved c f s) :=
  let ranged: (a: Nat) → (b: Nat) → List.Mem (a, b) (List.append done [(f, s)]) → And (a < n) (b < n) :=
    a b m => memSnoc a b (f, s) done m (And (a < n) (b < n)) (o => inv.inRange a b o)
      (e => Both (rewrite And.left e in hf) (rewrite And.right e in hs))
  let more: (a: Nat) → (b: Nat) → Joined done a b → Joined (List.append done [(f, s)]) a b := a b j => joinedAppend done [(f, s)] a b j
  {
    stored = b h => rewrite movedStored c f s n inv.stored b h in rfl,
    inRange = ranged,
    agree = a b m =>
      let both := ranged a b m
      rewrite movedLabel c f s n inv.stored a (And.left both), movedLabel c f s n inv.stored b (And.right both) in
        memSnoc a b (f, s) done m (relabel (c.labelOf f) (c.labelOf s) (c.labelOf a) = relabel (c.labelOf f) (c.labelOf s) (c.labelOf b))
          (o => rewrite inv.agree a b o in rfl)
          (ab => rewrite And.left ab, And.right ab, relabelFrom (c.labelOf f) (c.labelOf s), relabelTo (c.labelOf f) (c.labelOf s) differ in rfl),
    labelJoined = b h =>
      rewrite movedLabel c f s n inv.stored b h in
        match g: c.labelOf b == c.labelOf f with
          | True =>
            -- b is in f's circuit: b to its label, which is f's, back to
            -- f, along the new connection to s, and on to s's label.
            let toF: Joined done b f := Chain (inv.labelJoined b h) (rewrite DecEq.sound (c.labelOf b) (c.labelOf f) g in Backwards (inv.labelJoined f hf))
            Chain (more b f toF) (Chain (Connected (memLast (f, s) done)) (more s (c.labelOf s) (inv.labelJoined s hs)))
          | False => more b (c.labelOf b) (inv.labelJoined b h)
  }

theorem labelledJoin (n: Nat) (done: List (Nat, Nat)) (c: Circuits) (f: Nat) (s: Nat) (hf: f < n) (hs: s < n) (inv: Labelled n done c):
    Labelled n (List.append done [(f, s)]) (c.join f s) :=
  match e: c.labelOf f == c.labelOf s with
    | True =>
      -- The two boxes are already in one circuit: the labels stay.
      {
        stored = inv.stored,
        inRange = a b m => memSnoc a b (f, s) done m (And (a < n) (b < n)) (o => inv.inRange a b o)
          (ab => Both (rewrite And.left ab in hf) (rewrite And.right ab in hs)),
        agree = a b m => memSnoc a b (f, s) done m (c.labelOf a = c.labelOf b) (o => inv.agree a b o)
          (ab => rewrite And.left ab, And.right ab in DecEq.sound (c.labelOf f) (c.labelOf s) e),
        labelJoined = b h => joinedAppend done [(f, s)] b (c.labelOf b) (inv.labelJoined b h)
      }
    | False => labelledMoved n done c f s hf hs e inv

-- Joining a list of connections keeps them.
theorem labelledJoinAll (n: Nat): (rest: List (Nat, Nat)) → (done: List (Nat, Nat)) → (c: Circuits) →
    List.all rest (boxesBelow n) = True → Labelled n done c →
    Labelled n (List.append done rest) (joinAll c rest)
  | Nil, done, c, ok, inv => rewrite List.appendNil done in inv
  | Cons (f, s) rest, done, c, ok, inv =>
    match r: boxesBelow n (f, s) with
      | True =>
        rewrite <- List.appendAssoc done [(f, s)] rest in
          labelledJoinAll n rest (List.append done [(f, s)]) (c.join f s) ok
            (labelledJoin n done c f s (Bool.andLeft _ _ r) (Bool.andRight _ _ r) inv)
      | False => Void.exfalso (Bool.falseNotTrue ok)

-- The label theorem -----------------------------------------------------------

-- Two boxes have the same label exactly when they're joined.
theorem labelsTellOf (n: Nat) (done: List (Nat, Nat)) (c: Circuits) (inv: Labelled n done c):
    Tells n done (a b => c.labelOf a == c.labelOf b) :=
  a b ha hb => {
    forward = same => Chain (inv.labelJoined a ha) (rewrite DecEq.sound (c.labelOf a) (c.labelOf b) same in Backwards (inv.labelJoined b hb)),
    backward = j => rewrite sameLabelOfJoined c.labelOf done inv.agree a b j in DecEq.refl (c.labelOf b)
  }

-- After joining any connections between the boxes 0 to n - 1, in order, two
-- of the boxes have the same label exactly when the connections join them.
theorem labelsTell (n: Nat) (connections: List (Nat, Nat)) (ok: List.all connections (boxesBelow n) = True):
    Tells n connections (a b => (joinAll (Circuits.separate n) connections).labelOf a == (joinAll (Circuits.separate n) connections).labelOf b) :=
  labelsTellOf n connections (joinAll (Circuits.separate n) connections) (labelledJoinAll n connections Nil (Circuits.separate n) ok (labelledAtStart n))
