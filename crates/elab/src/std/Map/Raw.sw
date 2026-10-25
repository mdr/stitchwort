-- `Map.Raw k v`: the representation of a `Map` (std/Map/Map.sw), a
-- weight-balanced binary search tree (Adams's trees, as in Haskell's
-- `Data.Map`) with the ordering of the keys in the type (docs/proposals/
-- interfaces.md §7.5, D169). The tree carries proofs that its keys are in
-- order (`Map.Tree.Ordered`) and that its stored sizes are right
-- (`Map.Tree.Sized`), erased at run time. Two raw maps with the same entries
-- can be different trees; `Map` is the quotient that identifies them
-- (docs/proposals/map-equality.md §8). What each operation does to the
-- entries, `Map.Raw.Equiv`, and the lemmas that each operation respects it
-- are in std/Map/Spec.sw.
-- Insertion, lookup and removal take O(log n) comparisons; `size` is O(1).
-- docs/proposals/map-set.md.

import Std (Eq)
import Map.Tree (Tip, Bin)
import Map.Tree.Shape (Keep, SingleL, DoubleL, SingleR, DoubleR)

-- The tree. Each node stores the number of keys under it.
type Map.Tree (k: Type) (v: Type): Type =
  | Tip
  | Bin (size: Nat) (left: Map.Tree k v) (key: k) (value: v) (right: Map.Tree k v)

def Map.Tree.size: Map.Tree k v -> Nat
  | Tip => 0
  | Bin s _ _ _ _ => s

-- A node, with its size worked out.
def Map.Tree.bin (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v): Map.Tree k v :=
  Bin (Succ (Map.Tree.size l + Map.Tree.size r)) l key value r

-- Rebalancing. `Map.Tree.shape` picks a rotation from the sizes alone, and
-- `Map.Tree.rebuild` performs it; a rotation that doesn't fit the tree's
-- shape just makes a node. So rebuilding keeps the keys in order whatever
-- the sizes say, and the proofs below never look at them.
type Map.Tree.Shape: Type =
  | Keep
  | SingleL
  | DoubleL
  | SingleR
  | DoubleR

def Map.Tree.singleL (l: Map.Tree k v) (key: k) (value: v): Map.Tree k v -> Map.Tree k v
  | Bin _ rl rk rv rr => Map.Tree.bin (Map.Tree.bin l key value rl) rk rv rr
  | Tip => Map.Tree.bin l key value Tip

def Map.Tree.doubleL (l: Map.Tree k v) (key: k) (value: v): Map.Tree k v -> Map.Tree k v
  | Bin _ (Bin _ rll rlk rlv rlr) rk rv rr =>
    Map.Tree.bin (Map.Tree.bin l key value rll) rlk rlv (Map.Tree.bin rlr rk rv rr)
  | r => Map.Tree.bin l key value r

@[noReceiver]
def Map.Tree.singleR (key: k) (value: v) (r: Map.Tree k v): Map.Tree k v -> Map.Tree k v
  | Bin _ ll lk lv lr => Map.Tree.bin ll lk lv (Map.Tree.bin lr key value r)
  | Tip => Map.Tree.bin Tip key value r

@[noReceiver]
def Map.Tree.doubleR (key: k) (value: v) (r: Map.Tree k v): Map.Tree k v -> Map.Tree k v
  | Bin _ ll lk lv (Bin _ lrl lrk lrv lrr) =>
    Map.Tree.bin (Map.Tree.bin ll lk lv lrl) lrk lrv (Map.Tree.bin lrr key value r)
  | l => Map.Tree.bin l key value r

@[noReceiver]
def Map.Tree.rebuild: Map.Tree.Shape -> Map.Tree k v -> k -> v -> Map.Tree k v -> Map.Tree k v
  | Keep, l, key, value, r => Map.Tree.bin l key value r
  | SingleL, l, key, value, r => Map.Tree.singleL l key value r
  | DoubleL, l, key, value, r => Map.Tree.doubleL l key value r
  | SingleR, l, key, value, r => Map.Tree.singleR key value r l
  | DoubleR, l, key, value, r => Map.Tree.doubleR key value r l

-- Single or double, by the sizes of the heavy side's children.
def Map.Tree.shapeL: Map.Tree k v -> Map.Tree.Shape
  | Bin _ rl _ _ rr => if Nat.leq (Succ (Map.Tree.size rl)) (Map.Tree.size rr * 2) then SingleL else DoubleL
  | Tip => Keep

def Map.Tree.shapeR: Map.Tree k v -> Map.Tree.Shape
  | Bin _ ll _ _ lr => if Nat.leq (Succ (Map.Tree.size lr)) (Map.Tree.size ll * 2) then SingleR else DoubleR
  | Tip => Keep

-- A rotation when one side has more than three times the other's keys
-- (Data.Map's delta 3 and ratio 2).
def Map.Tree.shape (l: Map.Tree k v) (r: Map.Tree k v): Map.Tree.Shape :=
  if Nat.leq (Map.Tree.size l + Map.Tree.size r) 1 then Keep
  else if Nat.leq (Succ (Map.Tree.size l * 3)) (Map.Tree.size r) then Map.Tree.shapeL r
  else if Nat.leq (Succ (Map.Tree.size r * 3)) (Map.Tree.size l) then Map.Tree.shapeR l
  else Keep

-- A node, rebalanced: `l` and `r` were balanced, and one has changed by at
-- most one key since.
def Map.Tree.balance (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v): Map.Tree k v :=
  Map.Tree.rebuild (Map.Tree.shape l r) l key value r

-- Operations on trees

-- `value` at `key`; if `key` is there already, `f value old`.
@[noReceiver]
def Map.Tree.insertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v): Map.Tree k v -> Map.Tree k v
  | Tip => Bin 1 Tip key value Tip
  | Bin s l kk vv r => match Ord.compare key kk with
    | Less => Map.Tree.balance (Map.Tree.insertWith f key value l) kk vv r
    | Equal => Bin s l kk (f value vv) r
    | Greater => Map.Tree.balance l kk vv (Map.Tree.insertWith f key value r)

@[noReceiver]
def Map.Tree.get [auto ord: Ord k] (key: k): Map.Tree k v -> Option v
  | Tip => None
  | Bin _ l kk vv r => match Ord.compare key kk with
    | Less => Map.Tree.get key l
    | Equal => Some vv
    | Greater => Map.Tree.get key r

-- The smallest key of a node whose key is `key` and whose left subtree is
-- the tree given, and its value.
@[noReceiver]
def Map.Tree.minKey (key: k): Map.Tree k v -> k
  | Tip => key
  | Bin _ l lk _ _ => Map.Tree.minKey lk l

@[noReceiver]
def Map.Tree.minValue (value: v): Map.Tree k v -> v
  | Tip => value
  | Bin _ l _ lv _ => Map.Tree.minValue lv l

-- The node `l key value r` without its smallest key.
def Map.Tree.deleteMin: Map.Tree k v -> k -> v -> Map.Tree k v -> Map.Tree k v
  | Tip, key, value, r => r
  | Bin _ ll lk lv lr, key, value, r => Map.Tree.balance (Map.Tree.deleteMin ll lk lv lr) key value r

-- Two trees, every key of the first below every key of the second, as one.
def Map.Tree.glue: Map.Tree k v -> Map.Tree k v -> Map.Tree k v
  | Tip, r => r
  | l, Tip => l
  | l, Bin _ rl rk rv rr =>
    Map.Tree.balance l (Map.Tree.minKey rk rl) (Map.Tree.minValue rv rl) (Map.Tree.deleteMin rl rk rv rr)

@[noReceiver]
def Map.Tree.remove [auto ord: Ord k] (key: k): Map.Tree k v -> Map.Tree k v
  | Tip => Tip
  | Bin s l kk vv r => match Ord.compare key kk with
    | Less => Map.Tree.balance (Map.Tree.remove key l) kk vv r
    | Equal => Map.Tree.glue l r
    | Greater => Map.Tree.balance l kk vv (Map.Tree.remove key r)

-- The entries in key order, followed by `acc`.
def Map.Tree.toListOnto: Map.Tree k v -> List (k, v) -> List (k, v)
  | Tip, acc => acc
  | Bin _ l kk vv r, acc => Map.Tree.toListOnto l (Cons (kk, vv) (Map.Tree.toListOnto r acc))

@[noReceiver]
def Map.Tree.foldLeft (f: b -> k -> v -> b): b -> Map.Tree k v -> b
  | z, Tip => z
  | z, Bin _ l kk vv r => Map.Tree.foldLeft f (f (Map.Tree.foldLeft f z l) kk vv) r

@[noReceiver]
def Map.Tree.map (f: v -> w): Map.Tree k v -> Map.Tree k w
  | Tip => Tip
  | Bin s l kk vv r => Bin s (Map.Tree.map f l) kk (f vv) (Map.Tree.map f r)

@[noReceiver]
def Map.Tree.mapWithKey (f: k -> v -> w): Map.Tree k v -> Map.Tree k w
  | Tip => Tip
  | Bin s l kk vv r => Bin s (Map.Tree.mapWithKey f l) kk (f kk vv) (Map.Tree.mapWithKey f r)

@[noReceiver]
def Map.Tree.minOr (found: Option (k, v)): Map.Tree k v -> Option (k, v)
  | Tip => found
  | Bin _ l kk vv r => Map.Tree.minOr (Some (kk, vv)) l

@[noReceiver]
def Map.Tree.maxOr (found: Option (k, v)): Map.Tree k v -> Option (k, v)
  | Tip => found
  | Bin _ l kk vv r => Map.Tree.maxOr (Some (kk, vv)) r

@[noReceiver]
def Map.Tree.nearestBelow [auto ord: Ord k] (key: k) (found: Option (k, v)): Map.Tree k v -> Option (k, v)
  | Tip => found
  | Bin _ l kk vv r => match Ord.compare kk key with
    | Less => Map.Tree.nearestBelow key (Some (kk, vv)) r
    | _ => Map.Tree.nearestBelow key found l

@[noReceiver]
def Map.Tree.nearestAbove [auto ord: Ord k] (key: k) (found: Option (k, v)): Map.Tree k v -> Option (k, v)
  | Tip => found
  | Bin _ l kk vv r => match Ord.compare key kk with
    | Less => Map.Tree.nearestAbove key (Some (kk, vv)) l
    | _ => Map.Tree.nearestAbove key found r

-- Keys in order

-- `lo < x`, where no bound is below everything.
def Map.Tree.Above (ord: Ord k): Option k -> k -> Prop
  | None, x => Unit
  | Some lo, x => Ord.compare lo x = Less

-- `x < hi`.
def Map.Tree.Below (ord: Ord k) (x: k): Option k -> Prop
  | None => Unit
  | Some hi => Ord.compare x hi = Less

-- Every key is strictly between the bounds, and in order: a binary search tree.
@[noReceiver]
def Map.Tree.Within (ord: Ord k): Option k -> Option k -> Map.Tree k v -> Prop
  | lo, hi, Tip => Unit
  | lo, hi, Bin _ l kk _ r =>
    And (And (Map.Tree.Above ord lo kk) (Map.Tree.Below ord kk hi))
      (And (Map.Tree.Within ord lo (Some kk) l) (Map.Tree.Within ord (Some kk) hi r))

-- The keys are in order by `ord`.
@[noReceiver]
def Map.Tree.Ordered (ord: Ord k) (t: Map.Tree k v): Prop := Map.Tree.Within ord None None t

-- Each node's stored size is the number of keys under it, so `size` counts
-- the entries. Rebalancing reads the sizes, but `get`, `toList` and the
-- rest never depend on them; `Map.size` does.
def Map.Tree.Sized: Map.Tree k v -> Prop
  | Tip => Unit
  | Bin s l _ _ r => And (s = Succ (Map.Tree.size l + Map.Tree.size r)) (And (Map.Tree.Sized l) (Map.Tree.Sized r))

-- A raw map: a tree, the proof that its keys are in order, and the proof
-- that its stored sizes are right (both erased at run time).
type Map.Raw (k: Type) (v: Type) [auto ord: Ord k] = {
  tree: Map.Tree k v,
  ordered: Map.Tree.Ordered ord tree,
  sized: Map.Tree.Sized tree
}

-- Proofs: rebalancing, insertion and removal keep the keys in order.

theorem Map.Tree.aboveTrans (ord: Ord k): (lo: Option k) -> (a: k) -> (b: k) ->
    Map.Tree.Above ord lo a -> Ord.compare a b = Less -> Map.Tree.Above ord lo b
  | None, a, b, h, e => Trivial
  | Some x, a, b, h, e => ord.trans x a b h e

theorem Map.Tree.belowTrans (ord: Ord k): (hi: Option k) -> (a: k) -> (b: k) ->
    Ord.compare a b = Less -> Map.Tree.Below ord b hi -> Map.Tree.Below ord a hi
  | None, a, b, e, h => Trivial
  | Some y, a, b, e, h => ord.trans a b y e h

-- `compare y x` is `Less` when `compare x y` is `Greater`.
theorem Map.Tree.lessOfGreater (ord: Ord k) (x: k) (y: k) (e: Ord.compare x y = Greater):
    Ord.compare y x = Less :=
  Eq.trans (ord.flip x y) (Eq.cong Ordering.flip e)

-- `x <= y < z` gives `x < z`.
theorem Map.Tree.lessOfLeLess (ord: Ord k) (x: k) (y: k) (z: k)
    (h: Not (Ord.compare x y = Greater)) (e: Ord.compare y z = Less):
    Ord.compare x z = Less :=
  match c: Ord.compare x y with
    | Less => ord.trans x y z c e
    | Equal => rewrite ord.equal x y c in e
    | Greater => Void.exfalso (h rfl)

-- A tree within narrower bounds is within wider ones.
theorem Map.Tree.withinLow (ord: Ord k): (lo: Option k) -> (a: k) -> (hi: Option k) -> (t: Map.Tree k v) ->
    Map.Tree.Above ord lo a -> Map.Tree.Within ord (Some a) hi t -> Map.Tree.Within ord lo hi t
  | lo, a, hi, Tip, h, w => Trivial
  | lo, a, hi, Bin _ l kk _ r, h, Both (Both akk bkk) (Both wl wr) =>
    Both (Both (Map.Tree.aboveTrans ord lo a kk h akk) bkk) (Both (Map.Tree.withinLow ord lo a (Some kk) l h wl) wr)

theorem Map.Tree.withinHigh (ord: Ord k): (lo: Option k) -> (a: k) -> (hi: Option k) -> (t: Map.Tree k v) ->
    Map.Tree.Below ord a hi -> Map.Tree.Within ord lo (Some a) t -> Map.Tree.Within ord lo hi t
  | lo, a, hi, Tip, h, w => Trivial
  | lo, a, hi, Bin _ l kk _ r, h, Both (Both akk bkk) (Both wl wr) =>
    Both (Both akk (Map.Tree.belowTrans ord hi kk a bkk h)) (Both wl (Map.Tree.withinHigh ord (Some kk) a hi r h wr))

theorem Map.Tree.singleLWithin (ord: Ord k) (lo: Option k) (hi: Option k) (l: Map.Tree k v) (key: k) (value: v)
    (ab: Map.Tree.Above ord lo key) (wl: Map.Tree.Within ord lo (Some key) l):
    (r: Map.Tree k v) -> Map.Tree.Below ord key hi -> Map.Tree.Within ord (Some key) hi r ->
    Map.Tree.Within ord lo hi (Map.Tree.singleL l key value r)
  | Tip, be, wr => Both (Both ab be) (Both wl wr)
  | Bin _ rl rk rv rr, be, Both (Both krk brk) (Both wrl wrr) =>
    Both (Both (Map.Tree.aboveTrans ord lo key rk ab krk) brk) (Both (Both (Both ab krk) (Both wl wrl)) wrr)

theorem Map.Tree.doubleLWithin (ord: Ord k) (lo: Option k) (hi: Option k) (l: Map.Tree k v) (key: k) (value: v)
    (ab: Map.Tree.Above ord lo key) (wl: Map.Tree.Within ord lo (Some key) l):
    (r: Map.Tree k v) -> Map.Tree.Below ord key hi -> Map.Tree.Within ord (Some key) hi r ->
    Map.Tree.Within ord lo hi (Map.Tree.doubleL l key value r)
  | Tip, be, wr => Both (Both ab be) (Both wl wr)
  | Bin s Tip rk rv rr, be, wr => Both (Both ab be) (Both wl wr)
  | Bin _ (Bin _ rll rlk rlv rlr) rk rv rr, be,
      Both (Both krk brk) (Both (Both (Both krlk rlkrk) (Both wrll wrlr)) wrr) =>
    Both (Both (Map.Tree.aboveTrans ord lo key rlk ab krlk) (Map.Tree.belowTrans ord hi rlk rk rlkrk brk))
      (Both (Both (Both ab krlk) (Both wl wrll)) (Both (Both rlkrk brk) (Both wrlr wrr)))

theorem Map.Tree.singleRWithin (ord: Ord k) (lo: Option k) (hi: Option k) (key: k) (value: v) (r: Map.Tree k v)
    (be: Map.Tree.Below ord key hi) (wr: Map.Tree.Within ord (Some key) hi r):
    (l: Map.Tree k v) -> Map.Tree.Above ord lo key -> Map.Tree.Within ord lo (Some key) l ->
    Map.Tree.Within ord lo hi (Map.Tree.singleR key value r l)
  | Tip, ab, wl => Both (Both ab be) (Both wl wr)
  | Bin _ ll lk lv lr, ab, Both (Both alk lkk) (Both wll wlr) =>
    Both (Both alk (Map.Tree.belowTrans ord hi lk key lkk be)) (Both wll (Both (Both lkk be) (Both wlr wr)))

theorem Map.Tree.doubleRWithin (ord: Ord k) (lo: Option k) (hi: Option k) (key: k) (value: v) (r: Map.Tree k v)
    (be: Map.Tree.Below ord key hi) (wr: Map.Tree.Within ord (Some key) hi r):
    (l: Map.Tree k v) -> Map.Tree.Above ord lo key -> Map.Tree.Within ord lo (Some key) l ->
    Map.Tree.Within ord lo hi (Map.Tree.doubleR key value r l)
  | Tip, ab, wl => Both (Both ab be) (Both wl wr)
  | Bin s ll lk lv Tip, ab, wl => Both (Both ab be) (Both wl wr)
  | Bin _ ll lk lv (Bin _ lrl lrk lrv lrr), ab,
      Both (Both alk lkk) (Both wll (Both (Both lklrk lrkk) (Both wlrl wlrr))) =>
    Both (Both (Map.Tree.aboveTrans ord lo lk lrk alk lklrk) (Map.Tree.belowTrans ord hi lrk key lrkk be))
      (Both (Both (Both alk lklrk) (Both wll wlrl)) (Both (Both lrkk be) (Both wlrr wr)))

-- Rebuilding keeps the keys in order, whichever rotation is chosen.
theorem Map.Tree.rebuildWithin (ord: Ord k) (lo: Option k) (hi: Option k) (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi)
    (wl: Map.Tree.Within ord lo (Some key) l) (wr: Map.Tree.Within ord (Some key) hi r):
    (s: Map.Tree.Shape) -> Map.Tree.Within ord lo hi (Map.Tree.rebuild s l key value r)
  | Keep => Both (Both ab be) (Both wl wr)
  | SingleL => Map.Tree.singleLWithin ord lo hi l key value ab wl r be wr
  | DoubleL => Map.Tree.doubleLWithin ord lo hi l key value ab wl r be wr
  | SingleR => Map.Tree.singleRWithin ord lo hi key value r be wr l ab wl
  | DoubleR => Map.Tree.doubleRWithin ord lo hi key value r be wr l ab wl

theorem Map.Tree.balanceWithin (ord: Ord k) (lo: Option k) (hi: Option k) (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi)
    (wl: Map.Tree.Within ord lo (Some key) l) (wr: Map.Tree.Within ord (Some key) hi r):
    Map.Tree.Within ord lo hi (Map.Tree.balance l key value r) :=
  Map.Tree.rebuildWithin ord lo hi l key value r ab be wl wr (Map.Tree.shape l r)

theorem Map.Tree.insertWithWithin [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v):
    (lo: Option k) -> (hi: Option k) -> (t: Map.Tree k v) ->
    Map.Tree.Above ord lo key -> Map.Tree.Below ord key hi -> Map.Tree.Within ord lo hi t ->
    Map.Tree.Within ord lo hi (Map.Tree.insertWith f key value t)
  | lo, hi, Tip, ab, be, w => Both (Both ab be) (Both Trivial Trivial)
  | lo, hi, Bin s l kk vv r, ab, be, Both (Both akk bkk) (Both wl wr) =>
    match e: Ord.compare key kk with
      | Less => Map.Tree.balanceWithin ord lo hi (Map.Tree.insertWith f key value l) kk vv r akk bkk
        (Map.Tree.insertWithWithin f key value lo (Some kk) l ab e wl) wr
      | Equal => Both (Both akk bkk) (Both wl wr)
      | Greater => Map.Tree.balanceWithin ord lo hi l kk vv (Map.Tree.insertWith f key value r) akk bkk
        wl (Map.Tree.insertWithWithin f key value (Some kk) hi r (Map.Tree.lessOfGreater ord key kk e) be wr)

-- The smallest key is above whatever the node's key is above, and below
-- whatever it's below.
theorem Map.Tree.minKeyAbove (ord: Ord k) (lo: Option k): (key: k) -> (l: Map.Tree k v) ->
    Map.Tree.Above ord lo key -> Map.Tree.Within ord lo (Some key) l -> Map.Tree.Above ord lo (Map.Tree.minKey key l)
  | key, Tip, ab, w => ab
  | key, Bin _ ll lk _ lr, ab, Both (Both alk lkk) (Both wll wlr) => Map.Tree.minKeyAbove ord lo lk ll alk wll

theorem Map.Tree.minKeyBelow (ord: Ord k) (lo: Option k) (hi: Option k): (key: k) -> (l: Map.Tree k v) ->
    Map.Tree.Below ord key hi -> Map.Tree.Within ord lo (Some key) l -> Map.Tree.Below ord (Map.Tree.minKey key l) hi
  | key, Tip, be, w => be
  | key, Bin _ ll lk _ lr, be, Both (Both alk lkk) (Both wll wlr) =>
    Map.Tree.minKeyBelow ord lo hi lk ll (Map.Tree.belowTrans ord hi lk key lkk be) wll

theorem Map.Tree.deleteMinWithin (ord: Ord k) (lo: Option k) (hi: Option k):
    (l: Map.Tree k v) -> (key: k) -> (value: v) -> (r: Map.Tree k v) ->
    Map.Tree.Above ord lo key -> Map.Tree.Below ord key hi ->
    Map.Tree.Within ord lo (Some key) l -> Map.Tree.Within ord (Some key) hi r ->
    Map.Tree.Within ord (Some (Map.Tree.minKey key l)) hi (Map.Tree.deleteMin l key value r)
  | Tip, key, value, r, ab, be, wl, wr => wr
  | Bin _ ll lk lv lr, key, value, r, ab, be, Both (Both alk lkk) (Both wll wlr), wr =>
    Map.Tree.balanceWithin ord (Some (Map.Tree.minKey lk ll)) hi (Map.Tree.deleteMin ll lk lv lr) key value r
      (Map.Tree.minKeyBelow ord lo (Some key) lk ll lkk wll) be
      (Map.Tree.deleteMinWithin ord lo (Some key) ll lk lv lr alk lkk wll wlr) wr

theorem Map.Tree.glueWithin (ord: Ord k) (lo: Option k) (hi: Option k) (key: k)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi):
    (l: Map.Tree k v) -> (r: Map.Tree k v) ->
    Map.Tree.Within ord lo (Some key) l -> Map.Tree.Within ord (Some key) hi r ->
    Map.Tree.Within ord lo hi (Map.Tree.glue l r)
  | Tip, r, wl, wr => Map.Tree.withinLow ord lo key hi r ab wr
  | Bin s ll lk lv lr, Tip, wl, wr => Map.Tree.withinHigh ord lo key hi (Bin s ll lk lv lr) be wl
  | Bin s ll lk lv lr, Bin _ rl rk rv rr, wl, Both (Both krk brk) (Both wrl wrr) =>
    Map.Tree.balanceWithin ord lo hi (Bin s ll lk lv lr) (Map.Tree.minKey rk rl) (Map.Tree.minValue rv rl)
      (Map.Tree.deleteMin rl rk rv rr)
      (Map.Tree.aboveTrans ord lo key (Map.Tree.minKey rk rl) ab (Map.Tree.minKeyAbove ord (Some key) rk rl krk wrl))
      (Map.Tree.minKeyBelow ord (Some key) hi rk rl brk wrl)
      (Map.Tree.withinHigh ord lo key (Some (Map.Tree.minKey rk rl)) (Bin s ll lk lv lr)
        (Map.Tree.minKeyAbove ord (Some key) rk rl krk wrl) wl)
      (Map.Tree.deleteMinWithin ord (Some key) hi rl rk rv rr krk brk wrl wrr)

theorem Map.Tree.removeWithin [auto ord: Ord k] (key: k):
    (lo: Option k) -> (hi: Option k) -> (t: Map.Tree k v) ->
    Map.Tree.Within ord lo hi t -> Map.Tree.Within ord lo hi (Map.Tree.remove key t)
  | lo, hi, Tip, w => Trivial
  | lo, hi, Bin s l kk vv r, Both (Both akk bkk) (Both wl wr) =>
    match e: Ord.compare key kk with
      | Less => Map.Tree.balanceWithin ord lo hi (Map.Tree.remove key l) kk vv r akk bkk
        (Map.Tree.removeWithin key lo (Some kk) l wl) wr
      | Equal => Map.Tree.glueWithin ord lo hi kk akk bkk l r wl wr
      | Greater => Map.Tree.balanceWithin ord lo hi l kk vv (Map.Tree.remove key r) akk bkk
        wl (Map.Tree.removeWithin key (Some kk) hi r wr)

-- Changing the values doesn't move the keys.
theorem Map.Tree.mapWithin (ord: Ord k) (f: v -> w): (lo: Option k) -> (hi: Option k) -> (t: Map.Tree k v) ->
    Map.Tree.Within ord lo hi t -> Map.Tree.Within ord lo hi (Map.Tree.map f t)
  | lo, hi, Tip, w => Trivial
  | lo, hi, Bin s l kk vv r, Both b (Both wl wr) =>
    Both b (Both (Map.Tree.mapWithin ord f lo (Some kk) l wl) (Map.Tree.mapWithin ord f (Some kk) hi r wr))

theorem Map.Tree.mapWithKeyWithin (ord: Ord k) (f: k -> v -> w): (lo: Option k) -> (hi: Option k) -> (t: Map.Tree k v) ->
    Map.Tree.Within ord lo hi t -> Map.Tree.Within ord lo hi (Map.Tree.mapWithKey f t)
  | lo, hi, Tip, w => Trivial
  | lo, hi, Bin s l kk vv r, Both b (Both wl wr) =>
    Both b (Both (Map.Tree.mapWithKeyWithin ord f lo (Some kk) l wl) (Map.Tree.mapWithKeyWithin ord f (Some kk) hi r wr))

-- Proofs: every operation keeps the stored sizes right. `bin` works the
-- size out, and each rotation is built from `bin`s.

theorem Map.Tree.binSized (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (sl: Map.Tree.Sized l) (sr: Map.Tree.Sized r): Map.Tree.Sized (Map.Tree.bin l key value r) :=
  Both rfl (Both sl sr)

theorem Map.Tree.singleLSized (l: Map.Tree k v) (key: k) (value: v) (sl: Map.Tree.Sized l):
    (r: Map.Tree k v) -> Map.Tree.Sized r -> Map.Tree.Sized (Map.Tree.singleL l key value r)
  | Tip, sr => Map.Tree.binSized l key value Tip sl sr
  | Bin _ rl rk rv rr, Both e (Both srl srr) =>
    Map.Tree.binSized (Map.Tree.bin l key value rl) rk rv rr (Map.Tree.binSized l key value rl sl srl) srr

theorem Map.Tree.doubleLSized (l: Map.Tree k v) (key: k) (value: v) (sl: Map.Tree.Sized l):
    (r: Map.Tree k v) -> Map.Tree.Sized r -> Map.Tree.Sized (Map.Tree.doubleL l key value r)
  | Tip, sr => Map.Tree.binSized l key value Tip sl sr
  | Bin s Tip rk rv rr, sr => Map.Tree.binSized l key value (Bin s Tip rk rv rr) sl sr
  | Bin _ (Bin _ rll rlk rlv rlr) rk rv rr, Both e (Both (Both e2 (Both srll srlr)) srr) =>
    Map.Tree.binSized (Map.Tree.bin l key value rll) rlk rlv (Map.Tree.bin rlr rk rv rr)
      (Map.Tree.binSized l key value rll sl srll) (Map.Tree.binSized rlr rk rv rr srlr srr)

theorem Map.Tree.singleRSized (key: k) (value: v) (r: Map.Tree k v) (sr: Map.Tree.Sized r):
    (l: Map.Tree k v) -> Map.Tree.Sized l -> Map.Tree.Sized (Map.Tree.singleR key value r l)
  | Tip, sl => Map.Tree.binSized Tip key value r sl sr
  | Bin _ ll lk lv lr, Both e (Both sll slr) =>
    Map.Tree.binSized ll lk lv (Map.Tree.bin lr key value r) sll (Map.Tree.binSized lr key value r slr sr)

theorem Map.Tree.doubleRSized (key: k) (value: v) (r: Map.Tree k v) (sr: Map.Tree.Sized r):
    (l: Map.Tree k v) -> Map.Tree.Sized l -> Map.Tree.Sized (Map.Tree.doubleR key value r l)
  | Tip, sl => Map.Tree.binSized Tip key value r sl sr
  | Bin s ll lk lv Tip, sl => Map.Tree.binSized (Bin s ll lk lv Tip) key value r sl sr
  | Bin _ ll lk lv (Bin _ lrl lrk lrv lrr), Both e (Both sll (Both e2 (Both slrl slrr))) =>
    Map.Tree.binSized (Map.Tree.bin ll lk lv lrl) lrk lrv (Map.Tree.bin lrr key value r)
      (Map.Tree.binSized ll lk lv lrl sll slrl) (Map.Tree.binSized lrr key value r slrr sr)

theorem Map.Tree.rebuildSized (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (sl: Map.Tree.Sized l) (sr: Map.Tree.Sized r):
    (s: Map.Tree.Shape) -> Map.Tree.Sized (Map.Tree.rebuild s l key value r)
  | Keep => Map.Tree.binSized l key value r sl sr
  | SingleL => Map.Tree.singleLSized l key value sl r sr
  | DoubleL => Map.Tree.doubleLSized l key value sl r sr
  | SingleR => Map.Tree.singleRSized key value r sr l sl
  | DoubleR => Map.Tree.doubleRSized key value r sr l sl

theorem Map.Tree.balanceSized (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (sl: Map.Tree.Sized l) (sr: Map.Tree.Sized r): Map.Tree.Sized (Map.Tree.balance l key value r) :=
  Map.Tree.rebuildSized l key value r sl sr (Map.Tree.shape l r)

theorem Map.Tree.insertWithSized [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v):
    (t: Map.Tree k v) -> Map.Tree.Sized t -> Map.Tree.Sized (Map.Tree.insertWith f key value t)
  | Tip, st => Both rfl (Both Trivial Trivial)
  | Bin s l kk vv r, Both e (Both sl sr) =>
    match c: Ord.compare key kk with
      | Less => Map.Tree.balanceSized (Map.Tree.insertWith f key value l) kk vv r (Map.Tree.insertWithSized f key value l sl) sr
      | Equal => Both e (Both sl sr)
      | Greater => Map.Tree.balanceSized l kk vv (Map.Tree.insertWith f key value r) sl (Map.Tree.insertWithSized f key value r sr)

theorem Map.Tree.deleteMinSized: (l: Map.Tree k v) -> (key: k) -> (value: v) -> (r: Map.Tree k v) ->
    Map.Tree.Sized l -> Map.Tree.Sized r -> Map.Tree.Sized (Map.Tree.deleteMin l key value r)
  | Tip, key, value, r, sl, sr => sr
  | Bin _ ll lk lv lr, key, value, r, Both e (Both sll slr), sr =>
    Map.Tree.balanceSized (Map.Tree.deleteMin ll lk lv lr) key value r (Map.Tree.deleteMinSized ll lk lv lr sll slr) sr

theorem Map.Tree.glueSized: (l: Map.Tree k v) -> (r: Map.Tree k v) ->
    Map.Tree.Sized l -> Map.Tree.Sized r -> Map.Tree.Sized (Map.Tree.glue l r)
  | Tip, r, sl, sr => sr
  | Bin s ll lk lv lr, Tip, sl, sr => sl
  | Bin s ll lk lv lr, Bin _ rl rk rv rr, sl, Both e (Both srl srr) =>
    Map.Tree.balanceSized (Bin s ll lk lv lr) (Map.Tree.minKey rk rl) (Map.Tree.minValue rv rl)
      (Map.Tree.deleteMin rl rk rv rr) sl (Map.Tree.deleteMinSized rl rk rv rr srl srr)

theorem Map.Tree.removeSized [auto ord: Ord k] (key: k):
    (t: Map.Tree k v) -> Map.Tree.Sized t -> Map.Tree.Sized (Map.Tree.remove key t)
  | Tip, st => Trivial
  | Bin s l kk vv r, Both e (Both sl sr) =>
    match c: Ord.compare key kk with
      | Less => Map.Tree.balanceSized (Map.Tree.remove key l) kk vv r (Map.Tree.removeSized key l sl) sr
      | Equal => Map.Tree.glueSized l r sl sr
      | Greater => Map.Tree.balanceSized l kk vv (Map.Tree.remove key r) sl (Map.Tree.removeSized key r sr)

theorem Map.Tree.sizeMap (f: v -> w): (t: Map.Tree k v) -> Map.Tree.size (Map.Tree.map f t) = Map.Tree.size t
  | Tip => rfl
  | Bin s l kk vv r => rfl

theorem Map.Tree.mapSized (f: v -> w): (t: Map.Tree k v) -> Map.Tree.Sized t -> Map.Tree.Sized (Map.Tree.map f t)
  | Tip, st => Trivial
  | Bin s l kk vv r, Both e (Both sl sr) =>
    Both (rewrite Map.Tree.sizeMap f l, Map.Tree.sizeMap f r in e)
      (Both (Map.Tree.mapSized f l sl) (Map.Tree.mapSized f r sr))

theorem Map.Tree.sizeMapWithKey (f: k -> v -> w): (t: Map.Tree k v) -> Map.Tree.size (Map.Tree.mapWithKey f t) = Map.Tree.size t
  | Tip => rfl
  | Bin s l kk vv r => rfl

theorem Map.Tree.mapWithKeySized (f: k -> v -> w): (t: Map.Tree k v) -> Map.Tree.Sized t -> Map.Tree.Sized (Map.Tree.mapWithKey f t)
  | Tip, st => Trivial
  | Bin s l kk vv r, Both e (Both sl sr) =>
    Both (rewrite Map.Tree.sizeMapWithKey f l, Map.Tree.sizeMapWithKey f r in e)
      (Both (Map.Tree.mapWithKeySized f l sl) (Map.Tree.mapWithKeySized f r sr))

-- Proofs: what `get` finds.

-- The value for the first entry with that key.
def Map.Tree.lookupList [auto ord: Ord k] (key: k): List (k, v) -> Option v
  | Nil => None
  | Cons (kk, vv) rest => match Ord.compare key kk with
    | Equal => Some vv
    | _ => Map.Tree.lookupList key rest

def Map.Tree.orElse: Option v -> Option v -> Option v
  | Some x, m => Some x
  | None, m => m

theorem Map.Tree.orElseNone: (m: Option v) -> Map.Tree.orElse m None = m
  | Some x => rfl
  | None => rfl

-- No key at or below the lower bound is in the tree.
theorem Map.Tree.getAbsentLow [auto ord: Ord k] (key: k): (lo: k) -> (hi: Option k) -> (t: Map.Tree k v) ->
    Map.Tree.Within ord (Some lo) hi t -> Not (Ord.compare key lo = Greater) -> Map.Tree.get key t = None
  | lo, hi, Tip, w, h => rfl
  | lo, hi, Bin s l kk vv r, Both (Both a b) (Both wl wr), h =>
    match e: Ord.compare key kk with
      | Less => Map.Tree.getAbsentLow key lo (Some kk) l wl h
      | Equal => Void.exfalso (Ordering.equalNotLess (Eq.trans (Eq.sym e) (Map.Tree.lessOfLeLess ord key lo kk h a)))
      | Greater => Void.exfalso (Ordering.greaterNotLess (Eq.trans (Eq.sym e) (Map.Tree.lessOfLeLess ord key lo kk h a)))

-- No key at or above the upper bound is in the tree.
theorem Map.Tree.getAbsentHigh [auto ord: Ord k] (key: k): (lo: Option k) -> (hi: k) -> (t: Map.Tree k v) ->
    Map.Tree.Within ord lo (Some hi) t -> Not (Ord.compare key hi = Less) -> Map.Tree.get key t = None
  | lo, hi, Tip, w, h => rfl
  | lo, hi, Bin s l kk vv r, Both (Both a b) (Both wl wr), h =>
    match e: Ord.compare key kk with
      | Less => Void.exfalso (h (ord.trans key kk hi e b))
      | Equal => Void.exfalso (h (rewrite ord.equal key kk e in b))
      | Greater => Map.Tree.getAbsentHigh key (Some kk) hi r wr h

-- `get` finds what a search of the entries in order finds.
theorem Map.Tree.lookupOnto [auto ord: Ord k] (key: k): (lo: Option k) -> (hi: Option k) -> (t: Map.Tree k v) -> (acc: List (k, v)) ->
    Map.Tree.Within ord lo hi t ->
    Map.Tree.lookupList key (Map.Tree.toListOnto t acc) = Map.Tree.orElse (Map.Tree.get key t) (Map.Tree.lookupList key acc)
  | lo, hi, Tip, acc, w => rfl
  | lo, hi, Bin s l kk vv r, acc, Both (Both a b) (Both wl wr) =>
    rewrite Map.Tree.lookupOnto key lo (Some kk) l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl in
    match e: Ord.compare key kk with
      | Less =>
        rewrite Map.Tree.lookupOnto key (Some kk) hi r acc wr,
          Map.Tree.getAbsentLow key kk hi r wr (x => Ordering.lessNotGreater (Eq.trans (Eq.sym e) x)) in rfl
      | Equal => rewrite Map.Tree.getAbsentHigh key lo kk l wl (x => Ordering.equalNotLess (Eq.trans (Eq.sym e) x)) in rfl
      | Greater =>
        rewrite Map.Tree.getAbsentHigh key lo kk l wl (x => Ordering.greaterNotLess (Eq.trans (Eq.sym e) x)),
          Map.Tree.lookupOnto key (Some kk) hi r acc wr in rfl

theorem Map.Tree.getLookup [auto ord: Ord k] (key: k) (lo: Option k) (hi: Option k) (t: Map.Tree k v)
    (w: Map.Tree.Within ord lo hi t): Map.Tree.get key t = Map.Tree.lookupList key (Map.Tree.toListOnto t Nil) :=
  Eq.sym (Eq.trans (Map.Tree.lookupOnto key lo hi t Nil w) (Map.Tree.orElseNone (Map.Tree.get key t)))

-- Rotations keep the entries in order.
theorem Map.Tree.rebuildOnto: (s: Map.Tree.Shape) -> (l: Map.Tree k v) -> (key: k) -> (value: v) -> (r: Map.Tree k v) ->
    (acc: List (k, v)) ->
    Map.Tree.toListOnto (Map.Tree.rebuild s l key value r) acc = Map.Tree.toListOnto (Map.Tree.bin l key value r) acc
  | Keep, l, key, value, r, acc => rfl
  | SingleL, l, key, value, Tip, acc => rfl
  | SingleL, l, key, value, Bin _ rl rk rv rr, acc => rfl
  | DoubleL, l, key, value, Tip, acc => rfl
  | DoubleL, l, key, value, Bin _ Tip rk rv rr, acc => rfl
  | DoubleL, l, key, value, Bin _ (Bin _ rll rlk rlv rlr) rk rv rr, acc => rfl
  | SingleR, Tip, key, value, r, acc => rfl
  | SingleR, Bin _ ll lk lv lr, key, value, r, acc => rfl
  | DoubleR, Tip, key, value, r, acc => rfl
  | DoubleR, Bin _ ll lk lv Tip, key, value, r, acc => rfl
  | DoubleR, Bin _ ll lk lv (Bin _ lrl lrk lrv lrr), key, value, r, acc => rfl

-- So `get` on a rebalanced node is `get` on the node.
theorem Map.Tree.getBalance [auto ord: Ord k] (key: k) (lo: Option k) (hi: Option k)
    (l: Map.Tree k v) (kk: k) (vv: v) (r: Map.Tree k v)
    (ab: Map.Tree.Above ord lo kk) (be: Map.Tree.Below ord kk hi)
    (wl: Map.Tree.Within ord lo (Some kk) l) (wr: Map.Tree.Within ord (Some kk) hi r):
    Map.Tree.get key (Map.Tree.balance l kk vv r) = Map.Tree.get key (Map.Tree.bin l kk vv r) :=
  Eq.trans (Map.Tree.getLookup key lo hi (Map.Tree.balance l kk vv r) (Map.Tree.balanceWithin ord lo hi l kk vv r ab be wl wr))
    (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.Tree.rebuildOnto (Map.Tree.shape l r) l kk vv r Nil))
      (Eq.sym (Map.Tree.getLookup key lo hi (Map.Tree.bin l kk vv r) (Both (Both ab be) (Both wl wr)))))

-- What `insertWith` stores: `value`, or `f value old`.
def Map.Tree.combine (f: v -> v -> v) (value: v): Option v -> v
  | None => value
  | Some old => f value old

theorem Map.Tree.getInsertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v):
    (lo: Option k) -> (hi: Option k) -> (t: Map.Tree k v) ->
    Map.Tree.Above ord lo key -> Map.Tree.Below ord key hi -> Map.Tree.Within ord lo hi t ->
    Map.Tree.get key (Map.Tree.insertWith f key value t) = Some (Map.Tree.combine f value (Map.Tree.get key t))
  | lo, hi, Tip, ab, be, w => rewrite Ord.compareSelf key in rfl
  | lo, hi, Bin s l kk vv r, ab, be, Both (Both akk bkk) (Both wl wr) =>
    match e: Ord.compare key kk with
      | Less =>
        rewrite Map.Tree.getBalance key lo hi (Map.Tree.insertWith f key value l) kk vv r akk bkk
          (Map.Tree.insertWithWithin f key value lo (Some kk) l ab e wl) wr, e in
        Map.Tree.getInsertWith f key value lo (Some kk) l ab e wl
      | Equal => rewrite e in rfl
      | Greater =>
        rewrite Map.Tree.getBalance key lo hi l kk vv (Map.Tree.insertWith f key value r) akk bkk
          wl (Map.Tree.insertWithWithin f key value (Some kk) hi r (Map.Tree.lessOfGreater ord key kk e) be wr), e in
        Map.Tree.getInsertWith f key value (Some kk) hi r (Map.Tree.lessOfGreater ord key kk e) be wr

theorem Map.Tree.getInsertWithOther [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (other: k)
    (ne: Not (other = key)):
    (lo: Option k) -> (hi: Option k) -> (t: Map.Tree k v) ->
    Map.Tree.Above ord lo key -> Map.Tree.Below ord key hi -> Map.Tree.Within ord lo hi t ->
    Map.Tree.get other (Map.Tree.insertWith f key value t) = Map.Tree.get other t
  | lo, hi, Tip, ab, be, w =>
    match e: Ord.compare other key with
      | Less => rfl
      | Equal => Void.exfalso (ne (ord.equal other key e))
      | Greater => rfl
  | lo, hi, Bin s l kk vv r, ab, be, Both (Both akk bkk) (Both wl wr) =>
    match e: Ord.compare key kk with
      | Less =>
        rewrite Map.Tree.getBalance other lo hi (Map.Tree.insertWith f key value l) kk vv r akk bkk
          (Map.Tree.insertWithWithin f key value lo (Some kk) l ab e wl) wr in
        match c: Ord.compare other kk with
          | Less => Map.Tree.getInsertWithOther f key value other ne lo (Some kk) l ab e wl
          | Equal => rfl
          | Greater => rfl
      | Equal =>
        match c: Ord.compare other kk with
          | Less => rfl
          | Equal => Void.exfalso (ne (Eq.trans (ord.equal other kk c) (Eq.sym (ord.equal key kk e))))
          | Greater => rfl
      | Greater =>
        rewrite Map.Tree.getBalance other lo hi l kk vv (Map.Tree.insertWith f key value r) akk bkk
          wl (Map.Tree.insertWithWithin f key value (Some kk) hi r (Map.Tree.lessOfGreater ord key kk e) be wr) in
        match c: Ord.compare other kk with
          | Less => rfl
          | Equal => rfl
          | Greater => Map.Tree.getInsertWithOther f key value other ne (Some kk) hi r (Map.Tree.lessOfGreater ord key kk e) be wr

theorem Map.Tree.combineFirst (value: v): (old: Option v) -> Map.Tree.combine (new o => new) value old = value
  | None => rfl
  | Some x => rfl

-- Raw maps

-- No entries.
def Map.Raw.empty [auto ord: Ord k]: Map.Raw k v := { tree = Tip, ordered = Trivial, sized = Trivial }

-- `value` at `key`; if `key` has a value already, `f value old` (so
-- `Map.insertWith counts key 1 Nat.add` counts).
@[noReceiver]
def Map.Raw.insertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (m: Map.Raw k v): Map.Raw k v := {
  tree = Map.Tree.insertWith f key value m.tree,
  ordered = Map.Tree.insertWithWithin f key value None None m.tree Trivial Trivial m.ordered,
  sized = Map.Tree.insertWithSized f key value m.tree m.sized
}

-- `value` at `key`, replacing any value there.
@[noReceiver]
def Map.Raw.insert [auto ord: Ord k] (key: k) (value: v) (m: Map.Raw k v): Map.Raw k v := Map.Raw.insertWith (new old => new) key value m

-- One entry.
def Map.Raw.singleton [auto ord: Ord k] (key: k) (value: v): Map.Raw k v := Map.Raw.insert key value Map.Raw.empty

-- The value at `key`, if there is one.
@[noReceiver]
def Map.Raw.get [auto ord: Ord k] (key: k) (m: Map.Raw k v): Option v := Map.Tree.get key m.tree

-- The value at `key`, or `d`.
@[noReceiver]
def Map.Raw.getOr [auto ord: Ord k] (d: v) (key: k) (m: Map.Raw k v): v := Option.getOrElse (Map.Raw.get key m) d

@[noReceiver]
def Map.Raw.contains [auto ord: Ord k] (key: k) (m: Map.Raw k v): Bool := match Map.Raw.get key m with
  | Some _ => True
  | None => False

-- Without `key` (the same map if it isn't there).
@[noReceiver]
def Map.Raw.remove [auto ord: Ord k] (key: k) (m: Map.Raw k v): Map.Raw k v := {
  tree = Map.Tree.remove key m.tree,
  ordered = Map.Tree.removeWithin key None None m.tree m.ordered,
  sized = Map.Tree.removeSized key m.tree m.sized
}

-- The value at `key` changed by `f`, which sees `None` when there's none
-- and removes the entry by returning `None`.
@[noReceiver]
def Map.Raw.alter [auto ord: Ord k] (f: Option v -> Option v) (key: k) (m: Map.Raw k v): Map.Raw k v :=
  match f (Map.Raw.get key m) with
    | None => Map.Raw.remove key m
    | Some value => Map.Raw.insert key value m

-- The value at `key` changed by `f`, if there is one.
@[noReceiver]
def Map.Raw.adjust [auto ord: Ord k] (f: v -> v) (key: k) (m: Map.Raw k v): Map.Raw k v :=
  match Map.Raw.get key m with
    | None => m
    | Some old => Map.Raw.insert key (f old) m

-- The number of entries, O(1).
def Map.Raw.size (m: Map.Raw k v [ord := o]): Nat := Map.Tree.size m.tree

def Map.Raw.isEmpty (m: Map.Raw k v [ord := o]): Bool := Nat.equal (Map.Raw.size m) 0

-- The entries, in key order.
def Map.Raw.toList (m: Map.Raw k v [ord := o]): List (k, v) := Map.Tree.toListOnto m.tree Nil

def Map.Raw.keys (m: Map.Raw k v [ord := o]): List k := List.map (Map.Raw.toList m) Pair.fst

def Map.Raw.values (m: Map.Raw k v [ord := o]): List v := List.map (Map.Raw.toList m) Pair.snd

-- A map of the pairs; a later pair's value replaces an earlier one's.
def Map.Raw.fromList [auto ord: Ord k] (xs: List (k, v)): Map.Raw k v :=
  List.foldLeft xs Map.Raw.empty (m entry => Map.Raw.insert entry.fst entry.snd m)

-- Left fold over the entries in key order: `f (f z k1 v1) k2 v2`.
@[noReceiver]
def Map.Raw.foldLeft (f: b -> k -> v -> b) (z: b) (m: Map.Raw k v [ord := o]): b := Map.Tree.foldLeft f z m.tree

-- Every value changed by `f`; the keys stay.
@[noReceiver]
def Map.Raw.map (f: v -> w) (m: Map.Raw k v [ord := o]): Map.Raw k w [ord := o] := {
  tree = Map.Tree.map f m.tree,
  ordered = Map.Tree.mapWithin o f None None m.tree m.ordered,
  sized = Map.Tree.mapSized f m.tree m.sized
}

@[noReceiver]
def Map.Raw.mapWithKey (f: k -> v -> w) (m: Map.Raw k v [ord := o]): Map.Raw k w [ord := o] := {
  tree = Map.Tree.mapWithKey f m.tree,
  ordered = Map.Tree.mapWithKeyWithin o f None None m.tree m.ordered,
  sized = Map.Tree.mapWithKeySized f m.tree m.sized
}

def Map.Raw.min (m: Map.Raw k v [ord := o]): Option (k, v) := Map.Tree.minOr None m.tree

def Map.Raw.max (m: Map.Raw k v [ord := o]): Option (k, v) := Map.Tree.maxOr None m.tree

@[noReceiver]
def Map.Raw.below [auto ord: Ord k] (key: k) (m: Map.Raw k v): Option (k, v) := Map.Tree.nearestBelow key None m.tree

@[noReceiver]
def Map.Raw.above [auto ord: Ord k] (key: k) (m: Map.Raw k v): Option (k, v) := Map.Tree.nearestAbove key None m.tree

-- What `get` says about `insert`, whatever the map was.

theorem Map.Raw.getEmpty [auto ord: Ord k] (key: k): Map.Raw.get key (Map.Raw.empty: Map.Raw k v) = None := rfl

theorem Map.Raw.getInsert [auto ord: Ord k] (key: k) (value: v) (m: Map.Raw k v):
    Map.Raw.get key (Map.Raw.insert key value m) = Some value :=
  Eq.trans (Map.Tree.getInsertWith (new old => new) key value None None m.tree Trivial Trivial m.ordered)
    (Eq.cong Some (Map.Tree.combineFirst value (Map.Raw.get key m)))

theorem Map.Raw.getInsertOther [auto ord: Ord k] (key: k) (value: v) (other: k) (ne: Not (other = key)) (m: Map.Raw k v):
    Map.Raw.get other (Map.Raw.insert key value m) = Map.Raw.get other m :=
  Map.Tree.getInsertWithOther (new old => new) key value other ne None None m.tree Trivial Trivial m.ordered

theorem Map.Raw.getInsertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (m: Map.Raw k v):
    Map.Raw.get key (Map.Raw.insertWith f key value m) = Some (Map.Tree.combine f value (Map.Raw.get key m)) :=
  Map.Tree.getInsertWith f key value None None m.tree Trivial Trivial m.ordered

theorem Map.Raw.getInsertWithOther [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (other: k) (ne: Not (other = key)) (m: Map.Raw k v):
    Map.Raw.get other (Map.Raw.insertWith f key value m) = Map.Raw.get other m :=
  Map.Tree.getInsertWithOther f key value other ne None None m.tree Trivial Trivial m.ordered

-- What `get` says about `map`: it finds what it did, with `f` applied.
-- (The tree's keys stay where they are, so the proof needs no ordering facts.)
theorem Map.Tree.getMap [auto ord: Ord k]: (t: Map.Tree k v) -> (key: k) -> (f: v -> w) ->
    Map.Tree.get key (Map.Tree.map f t) = Option.map (Map.Tree.get key t) f
  | Tip, key, f => rfl
  | Bin s l kk vv r, key, f =>
    match e: Ord.compare key kk with
      | Less => Map.Tree.getMap l key f
      | Equal => rfl
      | Greater => Map.Tree.getMap r key f

theorem Map.Raw.getMap [auto ord: Ord k] (m: Map.Raw k v) (key: k) (f: v -> w): Map.Raw.get key (Map.Raw.map f m) = Option.map (Map.Raw.get key m) f :=
  Map.Tree.getMap m.tree key f

theorem Map.Tree.getMapWithKey [auto ord: Ord k]: (t: Map.Tree k v) -> (key: k) -> (f: k -> v -> w) ->
    Map.Tree.get key (Map.Tree.mapWithKey f t) = Option.map (Map.Tree.get key t) (f key)
  | Tip, key, f => rfl
  | Bin s l kk vv r, key, f =>
    match e: Ord.compare key kk with
      | Less => Map.Tree.getMapWithKey l key f
      | Equal => rewrite ord.equal key kk e in rfl
      | Greater => Map.Tree.getMapWithKey r key f

theorem Map.Raw.getMapWithKey [auto ord: Ord k] (m: Map.Raw k v) (key: k) (f: k -> v -> w):
    Map.Raw.get key (Map.Raw.mapWithKey f m) = Option.map (Map.Raw.get key m) (f key) :=
  Map.Tree.getMapWithKey m.tree key f

-- The value of the last pair with that key, which is what `fromList` keeps.
def Map.lookupLast [auto ord: Ord k] (key: k): List (k, v) -> Option v
  | Nil => None
  | Cons (kk, vv) rest => match Map.lookupLast key rest with
    | Some x => Some x
    | None => match Ord.compare key kk with
      | Equal => Some vv
      | _ => None

-- Adding the pairs to any map: the last pair with the key wins, and if there is none, the map's value stays.
theorem Map.Raw.getFoldInsert [auto ord: Ord k]: (m: Map.Raw k v) -> (key: k) -> (xs: List (k, v)) ->
    Map.Raw.get key (List.foldLeft xs m (acc entry => Map.Raw.insert entry.fst entry.snd acc))
      = Map.Tree.orElse (Map.lookupLast key xs) (Map.Raw.get key m)
  | m, key, Nil => rfl
  | m, key, Cons (kk, vv) rest =>
    rewrite Map.Raw.getFoldInsert (Map.Raw.insert kk vv m) key rest in
    match found: Map.lookupLast key rest with
      | Some x => rfl
      | None =>
        match e: Ord.compare key kk with
          | Less => rewrite Map.Raw.getInsertOther kk vv key (x => Ordering.lessNotEqual (Eq.trans (Eq.sym e) (rewrite x in Ord.compareSelf kk))) m in rfl
          | Equal => rewrite ord.equal key kk e, Map.Raw.getInsert kk vv m in rfl
          | Greater => rewrite Map.Raw.getInsertOther kk vv key (x => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) (rewrite x in Ord.compareSelf kk))) m in rfl

-- What `get` says about `fromList`.
theorem Map.Raw.getFromList [auto ord: Ord k] (key: k) (xs: List (k, v)): Map.Raw.get key (Map.Raw.fromList xs) = Map.lookupLast key xs :=
  Eq.trans (Map.Raw.getFoldInsert Map.Raw.empty key xs) (Map.Tree.orElseNone (Map.lookupLast key xs))

def Map.Raw.example: Map.Raw Nat Text := Map.Raw.fromList [(3, "c"), (1, "a"), (2, "b")]

test "raw map: toList is in key order" := Map.Raw.toList Map.Raw.example == [(1, "a"), (2, "b"), (3, "c")]
test "raw map: get" := Map.Raw.get 2 Map.Raw.example == Some "b" && Map.Raw.get 4 Map.Raw.example == None
test "raw map: getOr" := Map.Raw.getOr "?" 4 Map.Raw.example == "?"
test "raw map: contains" := Map.Raw.contains 1 Map.Raw.example && !(Map.Raw.contains 0 Map.Raw.example)
test "raw map: insert replaces" := Map.Raw.toList (Map.Raw.insert 2 "B" Map.Raw.example) == [(1, "a"), (2, "B"), (3, "c")]
test "raw map: insertWith counts" :=
  Map.Raw.toList (List.foldLeft ['b', 'a', 'b'] Map.Raw.empty (m c => Map.Raw.insertWith Nat.add c 1 m)) == [('a', 1), ('b', 2)]
test "raw map: remove" := Map.Raw.toList (Map.Raw.remove 2 Map.Raw.example) == [(1, "a"), (3, "c")] && Map.Raw.size (Map.Raw.remove 9 Map.Raw.example) == 3
test "raw map: alter" := Map.Raw.toList (Map.Raw.alter (old => None) 1 (Map.Raw.alter (old => Some "d") 4 Map.Raw.example)) == [(2, "b"), (3, "c"), (4, "d")]
test "raw map: adjust" := Map.Raw.get 3 (Map.Raw.adjust (t => Text.append t "!") 3 Map.Raw.example) == Some "c!"
test "raw map: size" := Map.Raw.size Map.Raw.example == 3 && Map.Raw.isEmpty (Map.Raw.empty: Map.Raw Nat Nat)
test "raw map: keys and values" := Map.Raw.keys Map.Raw.example == [1, 2, 3] && Map.Raw.values Map.Raw.example == ["a", "b", "c"]
test "raw map: fromList, later wins" := Map.Raw.toList (Map.Raw.fromList [(1, 1), (1, 2)]) == [(1, 2)]
test "raw map: foldLeft" := Map.Raw.foldLeft (acc key t => acc + key) 0 Map.Raw.example == 6
test "raw map: map" := Map.Raw.values (Map.Raw.map Text.length Map.Raw.example) == [1, 1, 1]
test "raw map: get after map" := Map.Raw.get 2 (Map.Raw.map Text.length Map.Raw.example) == Some 1 && Map.Raw.get 4 (Map.Raw.map Text.length Map.Raw.example) == None
test "raw map: lookupLast, later wins" := Map.lookupLast 1 [(1, "a"), (2, "b"), (1, "c")] == Some "c" && Map.lookupLast 3 [(1, "a")] == None
