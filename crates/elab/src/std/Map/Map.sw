-- `Map k v`: finite maps from keys to values, kept as a weight-balanced
-- binary search tree (Adams's trees, as in Haskell's `Data.Map`), with the
-- ordering of the keys in the map's type (docs/proposals/interfaces.md
-- §7.5, D169): `Map Text Nat` is `Map Text Nat [ord := Text.instOrd]`, and a
-- map built with another ordering has another type. The tree carries a
-- proof that its keys are in order (`Map.Tree.Ordered`), erased at run time.
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
  | Tip           => 0
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
  | Tip               => Map.Tree.bin l key value Tip

def Map.Tree.doubleL (l: Map.Tree k v) (key: k) (value: v): Map.Tree k v -> Map.Tree k v
  | Bin _ (Bin _ rll rlk rlv rlr) rk rv rr =>
    Map.Tree.bin (Map.Tree.bin l key value rll) rlk rlv (Map.Tree.bin rlr rk rv rr)
  | r => Map.Tree.bin l key value r

def Map.Tree.singleR (key: k) (value: v) (r: Map.Tree k v): Map.Tree k v -> Map.Tree k v
  | Bin _ ll lk lv lr => Map.Tree.bin ll lk lv (Map.Tree.bin lr key value r)
  | Tip               => Map.Tree.bin Tip key value r

def Map.Tree.doubleR (key: k) (value: v) (r: Map.Tree k v): Map.Tree k v -> Map.Tree k v
  | Bin _ ll lk lv (Bin _ lrl lrk lrv lrr) =>
    Map.Tree.bin (Map.Tree.bin ll lk lv lrl) lrk lrv (Map.Tree.bin lrr key value r)
  | l => Map.Tree.bin l key value r

def Map.Tree.rebuild: Map.Tree.Shape -> Map.Tree k v -> k -> v -> Map.Tree k v -> Map.Tree k v
  | Keep,    l, key, value, r => Map.Tree.bin l key value r
  | SingleL, l, key, value, r => Map.Tree.singleL l key value r
  | DoubleL, l, key, value, r => Map.Tree.doubleL l key value r
  | SingleR, l, key, value, r => Map.Tree.singleR key value r l
  | DoubleR, l, key, value, r => Map.Tree.doubleR key value r l

-- Single or double, by the sizes of the heavy side's children.
def Map.Tree.shapeL: Map.Tree k v -> Map.Tree.Shape
  | Bin _ rl _ _ rr => if Nat.leq (Succ (Map.Tree.size rl)) (Map.Tree.size rr * 2) then SingleL else DoubleL
  | Tip             => Keep

def Map.Tree.shapeR: Map.Tree k v -> Map.Tree.Shape
  | Bin _ ll _ _ lr => if Nat.leq (Succ (Map.Tree.size lr)) (Map.Tree.size ll * 2) then SingleR else DoubleR
  | Tip             => Keep

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
def Map.Tree.insertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v): Map.Tree k v -> Map.Tree k v
  | Tip => Bin 1 Tip key value Tip
  | Bin s l kk vv r => match Ord.compare key kk with
    | Less    => Map.Tree.balance (Map.Tree.insertWith f key value l) kk vv r
    | Equal   => Bin s l kk (f value vv) r
    | Greater => Map.Tree.balance l kk vv (Map.Tree.insertWith f key value r)

def Map.Tree.get [auto ord: Ord k] (key: k): Map.Tree k v -> Maybe v
  | Tip => Nothing
  | Bin _ l kk vv r => match Ord.compare key kk with
    | Less    => Map.Tree.get key l
    | Equal   => Just vv
    | Greater => Map.Tree.get key r

-- The smallest key of a node whose key is `key` and whose left subtree is
-- the tree given, and its value.
def Map.Tree.minKey (key: k): Map.Tree k v -> k
  | Tip              => key
  | Bin _ l lk _ _   => Map.Tree.minKey lk l

def Map.Tree.minValue (value: v): Map.Tree k v -> v
  | Tip              => value
  | Bin _ l _ lv _   => Map.Tree.minValue lv l

-- The node `l key value r` without its smallest key.
def Map.Tree.deleteMin: Map.Tree k v -> k -> v -> Map.Tree k v -> Map.Tree k v
  | Tip,              key, value, r => r
  | Bin _ ll lk lv lr, key, value, r => Map.Tree.balance (Map.Tree.deleteMin ll lk lv lr) key value r

-- Two trees, every key of the first below every key of the second, as one.
def Map.Tree.glue: Map.Tree k v -> Map.Tree k v -> Map.Tree k v
  | Tip, r   => r
  | l,   Tip => l
  | l,   Bin _ rl rk rv rr =>
    Map.Tree.balance l (Map.Tree.minKey rk rl) (Map.Tree.minValue rv rl) (Map.Tree.deleteMin rl rk rv rr)

def Map.Tree.remove [auto ord: Ord k] (key: k): Map.Tree k v -> Map.Tree k v
  | Tip => Tip
  | Bin s l kk vv r => match Ord.compare key kk with
    | Less    => Map.Tree.balance (Map.Tree.remove key l) kk vv r
    | Equal   => Map.Tree.glue l r
    | Greater => Map.Tree.balance l kk vv (Map.Tree.remove key r)

-- The entries in key order, followed by `acc`.
def Map.Tree.toListOnto: Map.Tree k v -> List (k, v) -> List (k, v)
  | Tip,             acc => acc
  | Bin _ l kk vv r, acc => Map.Tree.toListOnto l (Cons (kk, vv) (Map.Tree.toListOnto r acc))

def Map.Tree.foldLeft (f: b -> k -> v -> b): b -> Map.Tree k v -> b
  | z, Tip             => z
  | z, Bin _ l kk vv r => Map.Tree.foldLeft f (f (Map.Tree.foldLeft f z l) kk vv) r

def Map.Tree.map (f: v -> w): Map.Tree k v -> Map.Tree k w
  | Tip             => Tip
  | Bin s l kk vv r => Bin s (Map.Tree.map f l) kk (f vv) (Map.Tree.map f r)

-- Keys in order

-- `lo < x`, where no bound is below everything.
def Map.Tree.Above (ord: Ord k): Maybe k -> k -> Prop
  | Nothing, x => Unit
  | Just lo, x => Ord.compare [ord := ord] lo x = Less

-- `x < hi`.
def Map.Tree.Below (ord: Ord k) (x: k): Maybe k -> Prop
  | Nothing => Unit
  | Just hi => Ord.compare [ord := ord] x hi = Less

-- Every key is strictly between the bounds, and in order: a binary search tree.
def Map.Tree.Within (ord: Ord k): Maybe k -> Maybe k -> Map.Tree k v -> Prop
  | lo, hi, Tip => Unit
  | lo, hi, Bin _ l kk _ r =>
    And (And (Map.Tree.Above ord lo kk) (Map.Tree.Below ord kk hi))
      (And (Map.Tree.Within ord lo (Just kk) l) (Map.Tree.Within ord (Just kk) hi r))

-- The keys are in order by `ord`.
def Map.Tree.Ordered (ord: Ord k) (t: Map.Tree k v): Prop := Map.Tree.Within ord Nothing Nothing t

-- The map itself: a tree, and the proof that its keys are in order.
type Map (k: Type) (v: Type) [auto ord: Ord k] =
  { tree: Map.Tree k v
  , ordered: Map.Tree.Ordered ord tree
  }

-- Proofs: rebalancing, insertion and removal keep the keys in order.

theorem Map.Tree.aboveTrans (ord: Ord k): (lo: Maybe k) -> (a: k) -> (b: k) ->
    Map.Tree.Above ord lo a -> Ord.compare [ord := ord] a b = Less -> Map.Tree.Above ord lo b
  | Nothing, a, b, h, e => Trivial
  | Just x,  a, b, h, e => ord.trans x a b h e

theorem Map.Tree.belowTrans (ord: Ord k): (hi: Maybe k) -> (a: k) -> (b: k) ->
    Ord.compare [ord := ord] a b = Less -> Map.Tree.Below ord b hi -> Map.Tree.Below ord a hi
  | Nothing, a, b, e, h => Trivial
  | Just y,  a, b, e, h => ord.trans a b y e h

-- `compare y x` is `Less` when `compare x y` is `Greater`.
theorem Map.Tree.lessOfGreater (ord: Ord k) (x: k) (y: k) (e: Ord.compare [ord := ord] x y = Greater):
    Ord.compare [ord := ord] y x = Less :=
  Eq.trans (ord.flip x y) (Eq.cong Ordering.flip e)

-- `x <= y < z` gives `x < z`.
theorem Map.Tree.lessOfLeLess (ord: Ord k) (x: k) (y: k) (z: k)
    (h: Not (Ord.compare [ord := ord] x y = Greater)) (e: Ord.compare [ord := ord] y z = Less):
    Ord.compare [ord := ord] x z = Less :=
  match c: Ord.compare [ord := ord] x y with
    | Less    => ord.trans x y z c e
    | Equal   => rewrite ord.equal x y c in e
    | Greater => Void.exfalso (h rfl)

-- A tree within narrower bounds is within wider ones.
theorem Map.Tree.withinLow (ord: Ord k): (lo: Maybe k) -> (a: k) -> (hi: Maybe k) -> (t: Map.Tree k v) ->
    Map.Tree.Above ord lo a -> Map.Tree.Within ord (Just a) hi t -> Map.Tree.Within ord lo hi t
  | lo, a, hi, Tip, h, w => Trivial
  | lo, a, hi, Bin _ l kk _ r, h, Both (Both akk bkk) (Both wl wr) =>
    Both (Both (Map.Tree.aboveTrans ord lo a kk h akk) bkk) (Both (Map.Tree.withinLow ord lo a (Just kk) l h wl) wr)

theorem Map.Tree.withinHigh (ord: Ord k): (lo: Maybe k) -> (a: k) -> (hi: Maybe k) -> (t: Map.Tree k v) ->
    Map.Tree.Below ord a hi -> Map.Tree.Within ord lo (Just a) t -> Map.Tree.Within ord lo hi t
  | lo, a, hi, Tip, h, w => Trivial
  | lo, a, hi, Bin _ l kk _ r, h, Both (Both akk bkk) (Both wl wr) =>
    Both (Both akk (Map.Tree.belowTrans ord hi kk a bkk h)) (Both wl (Map.Tree.withinHigh ord (Just kk) a hi r h wr))

theorem Map.Tree.singleLWithin (ord: Ord k) (lo: Maybe k) (hi: Maybe k) (l: Map.Tree k v) (key: k) (value: v)
    (ab: Map.Tree.Above ord lo key) (wl: Map.Tree.Within ord lo (Just key) l):
    (r: Map.Tree k v) -> Map.Tree.Below ord key hi -> Map.Tree.Within ord (Just key) hi r ->
    Map.Tree.Within ord lo hi (Map.Tree.singleL l key value r)
  | Tip, be, wr => Both (Both ab be) (Both wl wr)
  | Bin _ rl rk rv rr, be, Both (Both krk brk) (Both wrl wrr) =>
    Both (Both (Map.Tree.aboveTrans ord lo key rk ab krk) brk) (Both (Both (Both ab krk) (Both wl wrl)) wrr)

theorem Map.Tree.doubleLWithin (ord: Ord k) (lo: Maybe k) (hi: Maybe k) (l: Map.Tree k v) (key: k) (value: v)
    (ab: Map.Tree.Above ord lo key) (wl: Map.Tree.Within ord lo (Just key) l):
    (r: Map.Tree k v) -> Map.Tree.Below ord key hi -> Map.Tree.Within ord (Just key) hi r ->
    Map.Tree.Within ord lo hi (Map.Tree.doubleL l key value r)
  | Tip, be, wr => Both (Both ab be) (Both wl wr)
  | Bin s Tip rk rv rr, be, wr => Both (Both ab be) (Both wl wr)
  | Bin _ (Bin _ rll rlk rlv rlr) rk rv rr, be,
      Both (Both krk brk) (Both (Both (Both krlk rlkrk) (Both wrll wrlr)) wrr) =>
    Both (Both (Map.Tree.aboveTrans ord lo key rlk ab krlk) (Map.Tree.belowTrans ord hi rlk rk rlkrk brk))
      (Both (Both (Both ab krlk) (Both wl wrll)) (Both (Both rlkrk brk) (Both wrlr wrr)))

theorem Map.Tree.singleRWithin (ord: Ord k) (lo: Maybe k) (hi: Maybe k) (key: k) (value: v) (r: Map.Tree k v)
    (be: Map.Tree.Below ord key hi) (wr: Map.Tree.Within ord (Just key) hi r):
    (l: Map.Tree k v) -> Map.Tree.Above ord lo key -> Map.Tree.Within ord lo (Just key) l ->
    Map.Tree.Within ord lo hi (Map.Tree.singleR key value r l)
  | Tip, ab, wl => Both (Both ab be) (Both wl wr)
  | Bin _ ll lk lv lr, ab, Both (Both alk lkk) (Both wll wlr) =>
    Both (Both alk (Map.Tree.belowTrans ord hi lk key lkk be)) (Both wll (Both (Both lkk be) (Both wlr wr)))

theorem Map.Tree.doubleRWithin (ord: Ord k) (lo: Maybe k) (hi: Maybe k) (key: k) (value: v) (r: Map.Tree k v)
    (be: Map.Tree.Below ord key hi) (wr: Map.Tree.Within ord (Just key) hi r):
    (l: Map.Tree k v) -> Map.Tree.Above ord lo key -> Map.Tree.Within ord lo (Just key) l ->
    Map.Tree.Within ord lo hi (Map.Tree.doubleR key value r l)
  | Tip, ab, wl => Both (Both ab be) (Both wl wr)
  | Bin s ll lk lv Tip, ab, wl => Both (Both ab be) (Both wl wr)
  | Bin _ ll lk lv (Bin _ lrl lrk lrv lrr), ab,
      Both (Both alk lkk) (Both wll (Both (Both lklrk lrkk) (Both wlrl wlrr))) =>
    Both (Both (Map.Tree.aboveTrans ord lo lk lrk alk lklrk) (Map.Tree.belowTrans ord hi lrk key lrkk be))
      (Both (Both (Both alk lklrk) (Both wll wlrl)) (Both (Both lrkk be) (Both wlrr wr)))

-- Rebuilding keeps the keys in order, whichever rotation is chosen.
theorem Map.Tree.rebuildWithin (ord: Ord k) (lo: Maybe k) (hi: Maybe k) (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi)
    (wl: Map.Tree.Within ord lo (Just key) l) (wr: Map.Tree.Within ord (Just key) hi r):
    (s: Map.Tree.Shape) -> Map.Tree.Within ord lo hi (Map.Tree.rebuild s l key value r)
  | Keep    => Both (Both ab be) (Both wl wr)
  | SingleL => Map.Tree.singleLWithin ord lo hi l key value ab wl r be wr
  | DoubleL => Map.Tree.doubleLWithin ord lo hi l key value ab wl r be wr
  | SingleR => Map.Tree.singleRWithin ord lo hi key value r be wr l ab wl
  | DoubleR => Map.Tree.doubleRWithin ord lo hi key value r be wr l ab wl

theorem Map.Tree.balanceWithin (ord: Ord k) (lo: Maybe k) (hi: Maybe k) (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi)
    (wl: Map.Tree.Within ord lo (Just key) l) (wr: Map.Tree.Within ord (Just key) hi r):
    Map.Tree.Within ord lo hi (Map.Tree.balance l key value r) :=
  Map.Tree.rebuildWithin ord lo hi l key value r ab be wl wr (Map.Tree.shape l r)

theorem Map.Tree.insertWithWithin [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v):
    (lo: Maybe k) -> (hi: Maybe k) -> (t: Map.Tree k v) ->
    Map.Tree.Above ord lo key -> Map.Tree.Below ord key hi -> Map.Tree.Within ord lo hi t ->
    Map.Tree.Within ord lo hi (Map.Tree.insertWith f key value t)
  | lo, hi, Tip, ab, be, w => Both (Both ab be) (Both Trivial Trivial)
  | lo, hi, Bin s l kk vv r, ab, be, Both (Both akk bkk) (Both wl wr) =>
    match e: Ord.compare [ord := ord] key kk with
      | Less    => Map.Tree.balanceWithin ord lo hi (Map.Tree.insertWith f key value l) kk vv r akk bkk
          (Map.Tree.insertWithWithin f key value lo (Just kk) l ab e wl) wr
      | Equal   => Both (Both akk bkk) (Both wl wr)
      | Greater => Map.Tree.balanceWithin ord lo hi l kk vv (Map.Tree.insertWith f key value r) akk bkk
          wl (Map.Tree.insertWithWithin f key value (Just kk) hi r (Map.Tree.lessOfGreater ord key kk e) be wr)

-- The smallest key is above whatever the node's key is above, and below
-- whatever it's below.
theorem Map.Tree.minKeyAbove (ord: Ord k) (lo: Maybe k): (key: k) -> (l: Map.Tree k v) ->
    Map.Tree.Above ord lo key -> Map.Tree.Within ord lo (Just key) l -> Map.Tree.Above ord lo (Map.Tree.minKey key l)
  | key, Tip, ab, w => ab
  | key, Bin _ ll lk _ lr, ab, Both (Both alk lkk) (Both wll wlr) => Map.Tree.minKeyAbove ord lo lk ll alk wll

theorem Map.Tree.minKeyBelow (ord: Ord k) (lo: Maybe k) (hi: Maybe k): (key: k) -> (l: Map.Tree k v) ->
    Map.Tree.Below ord key hi -> Map.Tree.Within ord lo (Just key) l -> Map.Tree.Below ord (Map.Tree.minKey key l) hi
  | key, Tip, be, w => be
  | key, Bin _ ll lk _ lr, be, Both (Both alk lkk) (Both wll wlr) =>
    Map.Tree.minKeyBelow ord lo hi lk ll (Map.Tree.belowTrans ord hi lk key lkk be) wll

theorem Map.Tree.deleteMinWithin (ord: Ord k) (lo: Maybe k) (hi: Maybe k):
    (l: Map.Tree k v) -> (key: k) -> (value: v) -> (r: Map.Tree k v) ->
    Map.Tree.Above ord lo key -> Map.Tree.Below ord key hi ->
    Map.Tree.Within ord lo (Just key) l -> Map.Tree.Within ord (Just key) hi r ->
    Map.Tree.Within ord (Just (Map.Tree.minKey key l)) hi (Map.Tree.deleteMin l key value r)
  | Tip, key, value, r, ab, be, wl, wr => wr
  | Bin _ ll lk lv lr, key, value, r, ab, be, Both (Both alk lkk) (Both wll wlr), wr =>
    Map.Tree.balanceWithin ord (Just (Map.Tree.minKey lk ll)) hi (Map.Tree.deleteMin ll lk lv lr) key value r
      (Map.Tree.minKeyBelow ord lo (Just key) lk ll lkk wll) be
      (Map.Tree.deleteMinWithin ord lo (Just key) ll lk lv lr alk lkk wll wlr) wr

theorem Map.Tree.glueWithin (ord: Ord k) (lo: Maybe k) (hi: Maybe k) (key: k)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi):
    (l: Map.Tree k v) -> (r: Map.Tree k v) ->
    Map.Tree.Within ord lo (Just key) l -> Map.Tree.Within ord (Just key) hi r ->
    Map.Tree.Within ord lo hi (Map.Tree.glue l r)
  | Tip, r, wl, wr => Map.Tree.withinLow ord lo key hi r ab wr
  | Bin s ll lk lv lr, Tip, wl, wr => Map.Tree.withinHigh ord lo key hi (Bin s ll lk lv lr) be wl
  | Bin s ll lk lv lr, Bin _ rl rk rv rr, wl, Both (Both krk brk) (Both wrl wrr) =>
    Map.Tree.balanceWithin ord lo hi (Bin s ll lk lv lr) (Map.Tree.minKey rk rl) (Map.Tree.minValue rv rl)
      (Map.Tree.deleteMin rl rk rv rr)
      (Map.Tree.aboveTrans ord lo key (Map.Tree.minKey rk rl) ab (Map.Tree.minKeyAbove ord (Just key) rk rl krk wrl))
      (Map.Tree.minKeyBelow ord (Just key) hi rk rl brk wrl)
      (Map.Tree.withinHigh ord lo key (Just (Map.Tree.minKey rk rl)) (Bin s ll lk lv lr)
        (Map.Tree.minKeyAbove ord (Just key) rk rl krk wrl) wl)
      (Map.Tree.deleteMinWithin ord (Just key) hi rl rk rv rr krk brk wrl wrr)

theorem Map.Tree.removeWithin [auto ord: Ord k] (key: k):
    (lo: Maybe k) -> (hi: Maybe k) -> (t: Map.Tree k v) ->
    Map.Tree.Within ord lo hi t -> Map.Tree.Within ord lo hi (Map.Tree.remove key t)
  | lo, hi, Tip, w => Trivial
  | lo, hi, Bin s l kk vv r, Both (Both akk bkk) (Both wl wr) =>
    match e: Ord.compare [ord := ord] key kk with
      | Less    => Map.Tree.balanceWithin ord lo hi (Map.Tree.remove key l) kk vv r akk bkk
          (Map.Tree.removeWithin key lo (Just kk) l wl) wr
      | Equal   => Map.Tree.glueWithin ord lo hi kk akk bkk l r wl wr
      | Greater => Map.Tree.balanceWithin ord lo hi l kk vv (Map.Tree.remove key r) akk bkk
          wl (Map.Tree.removeWithin key (Just kk) hi r wr)

-- Changing the values doesn't move the keys.
theorem Map.Tree.mapWithin (ord: Ord k) (f: v -> w): (lo: Maybe k) -> (hi: Maybe k) -> (t: Map.Tree k v) ->
    Map.Tree.Within ord lo hi t -> Map.Tree.Within ord lo hi (Map.Tree.map f t)
  | lo, hi, Tip, w => Trivial
  | lo, hi, Bin s l kk vv r, Both b (Both wl wr) =>
    Both b (Both (Map.Tree.mapWithin ord f lo (Just kk) l wl) (Map.Tree.mapWithin ord f (Just kk) hi r wr))

-- Proofs: what `get` finds.

-- The value for the first entry with that key.
def Map.Tree.lookupList [auto ord: Ord k] (key: k): List (k, v) -> Maybe v
  | Nil => Nothing
  | Cons (kk, vv) rest => match Ord.compare key kk with
    | Equal => Just vv
    | _     => Map.Tree.lookupList key rest

def Map.Tree.orElse: Maybe v -> Maybe v -> Maybe v
  | Just x,  m => Just x
  | Nothing, m => m

theorem Map.Tree.orElseNothing: (m: Maybe v) -> Map.Tree.orElse m Nothing = m
  | Just x  => rfl
  | Nothing => rfl

-- No key at or below the lower bound is in the tree.
theorem Map.Tree.getAbsentLow [auto ord: Ord k] (key: k): (lo: k) -> (hi: Maybe k) -> (t: Map.Tree k v) ->
    Map.Tree.Within ord (Just lo) hi t -> Not (Ord.compare [ord := ord] key lo = Greater) -> Map.Tree.get key t = Nothing
  | lo, hi, Tip, w, h => rfl
  | lo, hi, Bin s l kk vv r, Both (Both a b) (Both wl wr), h =>
    match e: Ord.compare [ord := ord] key kk with
      | Less    => Map.Tree.getAbsentLow key lo (Just kk) l wl h
      | Equal   => Void.exfalso (Ordering.equalNotLess (Eq.trans (Eq.sym e) (Map.Tree.lessOfLeLess ord key lo kk h a)))
      | Greater => Void.exfalso (Ordering.greaterNotLess (Eq.trans (Eq.sym e) (Map.Tree.lessOfLeLess ord key lo kk h a)))

-- No key at or above the upper bound is in the tree.
theorem Map.Tree.getAbsentHigh [auto ord: Ord k] (key: k): (lo: Maybe k) -> (hi: k) -> (t: Map.Tree k v) ->
    Map.Tree.Within ord lo (Just hi) t -> Not (Ord.compare [ord := ord] key hi = Less) -> Map.Tree.get key t = Nothing
  | lo, hi, Tip, w, h => rfl
  | lo, hi, Bin s l kk vv r, Both (Both a b) (Both wl wr), h =>
    match e: Ord.compare [ord := ord] key kk with
      | Less    => Void.exfalso (h (ord.trans key kk hi e b))
      | Equal   => Void.exfalso (h (rewrite ord.equal key kk e in b))
      | Greater => Map.Tree.getAbsentHigh key (Just kk) hi r wr h

-- `get` finds what a search of the entries in order finds.
theorem Map.Tree.lookupOnto [auto ord: Ord k] (key: k): (lo: Maybe k) -> (hi: Maybe k) -> (t: Map.Tree k v) -> (acc: List (k, v)) ->
    Map.Tree.Within ord lo hi t ->
    Map.Tree.lookupList key (Map.Tree.toListOnto t acc) = Map.Tree.orElse (Map.Tree.get key t) (Map.Tree.lookupList key acc)
  | lo, hi, Tip, acc, w => rfl
  | lo, hi, Bin s l kk vv r, acc, Both (Both a b) (Both wl wr) =>
    rewrite Map.Tree.lookupOnto key lo (Just kk) l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl in
    match e: Ord.compare [ord := ord] key kk with
      | Less    =>
        rewrite Map.Tree.lookupOnto key (Just kk) hi r acc wr,
          Map.Tree.getAbsentLow key kk hi r wr (x => Ordering.lessNotGreater (Eq.trans (Eq.sym e) x)) in rfl
      | Equal   => rewrite Map.Tree.getAbsentHigh key lo kk l wl (x => Ordering.equalNotLess (Eq.trans (Eq.sym e) x)) in rfl
      | Greater =>
        rewrite Map.Tree.getAbsentHigh key lo kk l wl (x => Ordering.greaterNotLess (Eq.trans (Eq.sym e) x)),
          Map.Tree.lookupOnto key (Just kk) hi r acc wr in rfl

theorem Map.Tree.getLookup [auto ord: Ord k] (key: k) (lo: Maybe k) (hi: Maybe k) (t: Map.Tree k v)
    (w: Map.Tree.Within ord lo hi t): Map.Tree.get key t = Map.Tree.lookupList key (Map.Tree.toListOnto t Nil) :=
  Eq.sym (Eq.trans (Map.Tree.lookupOnto key lo hi t Nil w) (Map.Tree.orElseNothing (Map.Tree.get key t)))

-- Rotations keep the entries in order.
theorem Map.Tree.rebuildOnto: (s: Map.Tree.Shape) -> (l: Map.Tree k v) -> (key: k) -> (value: v) -> (r: Map.Tree k v) ->
    (acc: List (k, v)) ->
    Map.Tree.toListOnto (Map.Tree.rebuild s l key value r) acc = Map.Tree.toListOnto (Map.Tree.bin l key value r) acc
  | Keep,    l,                                   key, value, r,                                   acc => rfl
  | SingleL, l,                                   key, value, Tip,                                 acc => rfl
  | SingleL, l,                                   key, value, Bin _ rl rk rv rr,                   acc => rfl
  | DoubleL, l,                                   key, value, Tip,                                 acc => rfl
  | DoubleL, l,                                   key, value, Bin _ Tip rk rv rr,                  acc => rfl
  | DoubleL, l,                                   key, value, Bin _ (Bin _ rll rlk rlv rlr) rk rv rr, acc => rfl
  | SingleR, Tip,                                 key, value, r,                                   acc => rfl
  | SingleR, Bin _ ll lk lv lr,                   key, value, r,                                   acc => rfl
  | DoubleR, Tip,                                 key, value, r,                                   acc => rfl
  | DoubleR, Bin _ ll lk lv Tip,                  key, value, r,                                   acc => rfl
  | DoubleR, Bin _ ll lk lv (Bin _ lrl lrk lrv lrr), key, value, r,                                acc => rfl

-- So `get` on a rebalanced node is `get` on the node.
theorem Map.Tree.getBalance [auto ord: Ord k] (key: k) (lo: Maybe k) (hi: Maybe k)
    (l: Map.Tree k v) (kk: k) (vv: v) (r: Map.Tree k v)
    (ab: Map.Tree.Above ord lo kk) (be: Map.Tree.Below ord kk hi)
    (wl: Map.Tree.Within ord lo (Just kk) l) (wr: Map.Tree.Within ord (Just kk) hi r):
    Map.Tree.get key (Map.Tree.balance l kk vv r) = Map.Tree.get key (Map.Tree.bin l kk vv r) :=
  Eq.trans (Map.Tree.getLookup key lo hi (Map.Tree.balance l kk vv r) (Map.Tree.balanceWithin ord lo hi l kk vv r ab be wl wr))
    (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.Tree.rebuildOnto (Map.Tree.shape l r) l kk vv r Nil))
      (Eq.sym (Map.Tree.getLookup key lo hi (Map.Tree.bin l kk vv r) (Both (Both ab be) (Both wl wr)))))

-- What `insertWith` stores: `value`, or `f value old`.
def Map.Tree.combine (f: v -> v -> v) (value: v): Maybe v -> v
  | Nothing  => value
  | Just old => f value old

theorem Map.Tree.getInsertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v):
    (lo: Maybe k) -> (hi: Maybe k) -> (t: Map.Tree k v) ->
    Map.Tree.Above ord lo key -> Map.Tree.Below ord key hi -> Map.Tree.Within ord lo hi t ->
    Map.Tree.get key (Map.Tree.insertWith f key value t) = Just (Map.Tree.combine f value (Map.Tree.get key t))
  | lo, hi, Tip, ab, be, w => rewrite Ord.compareSelf [ord := ord] key in rfl
  | lo, hi, Bin s l kk vv r, ab, be, Both (Both akk bkk) (Both wl wr) =>
    match e: Ord.compare [ord := ord] key kk with
      | Less    =>
        rewrite Map.Tree.getBalance key lo hi (Map.Tree.insertWith f key value l) kk vv r akk bkk
          (Map.Tree.insertWithWithin f key value lo (Just kk) l ab e wl) wr, e in
        Map.Tree.getInsertWith f key value lo (Just kk) l ab e wl
      | Equal   => rewrite e in rfl
      | Greater =>
        rewrite Map.Tree.getBalance key lo hi l kk vv (Map.Tree.insertWith f key value r) akk bkk
          wl (Map.Tree.insertWithWithin f key value (Just kk) hi r (Map.Tree.lessOfGreater ord key kk e) be wr), e in
        Map.Tree.getInsertWith f key value (Just kk) hi r (Map.Tree.lessOfGreater ord key kk e) be wr

theorem Map.Tree.getInsertWithOther [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (other: k)
    (ne: Not (other = key)):
    (lo: Maybe k) -> (hi: Maybe k) -> (t: Map.Tree k v) ->
    Map.Tree.Above ord lo key -> Map.Tree.Below ord key hi -> Map.Tree.Within ord lo hi t ->
    Map.Tree.get other (Map.Tree.insertWith f key value t) = Map.Tree.get other t
  | lo, hi, Tip, ab, be, w =>
    match e: Ord.compare [ord := ord] other key with
      | Less    => rfl
      | Equal   => Void.exfalso (ne (ord.equal other key e))
      | Greater => rfl
  | lo, hi, Bin s l kk vv r, ab, be, Both (Both akk bkk) (Both wl wr) =>
    match e: Ord.compare [ord := ord] key kk with
      | Less    =>
        rewrite Map.Tree.getBalance other lo hi (Map.Tree.insertWith f key value l) kk vv r akk bkk
          (Map.Tree.insertWithWithin f key value lo (Just kk) l ab e wl) wr in
        match c: Ord.compare [ord := ord] other kk with
          | Less    => Map.Tree.getInsertWithOther f key value other ne lo (Just kk) l ab e wl
          | Equal   => rfl
          | Greater => rfl
      | Equal   =>
        match c: Ord.compare [ord := ord] other kk with
          | Less    => rfl
          | Equal   => Void.exfalso (ne (Eq.trans (ord.equal other kk c) (Eq.sym (ord.equal key kk e))))
          | Greater => rfl
      | Greater =>
        rewrite Map.Tree.getBalance other lo hi l kk vv (Map.Tree.insertWith f key value r) akk bkk
          wl (Map.Tree.insertWithWithin f key value (Just kk) hi r (Map.Tree.lessOfGreater ord key kk e) be wr) in
        match c: Ord.compare [ord := ord] other kk with
          | Less    => rfl
          | Equal   => rfl
          | Greater => Map.Tree.getInsertWithOther f key value other ne (Just kk) hi r (Map.Tree.lessOfGreater ord key kk e) be wr

theorem Map.Tree.combineFirst (value: v): (old: Maybe v) -> Map.Tree.combine (new o => new) value old = value
  | Nothing => rfl
  | Just x  => rfl

-- Maps

-- No entries.
def Map.empty [auto ord: Ord k]: Map k v := { tree = Tip, ordered = Trivial }

-- `value` at `key`; if `key` has a value already, `f value old` (so
-- `Map.insertWith Nat.add key 1 counts` counts).
def Map.insertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (m: Map k v): Map k v :=
  { tree = Map.Tree.insertWith f key value m.tree
  , ordered = Map.Tree.insertWithWithin f key value Nothing Nothing m.tree Trivial Trivial m.ordered
  }

-- `value` at `key`, replacing any value there.
def Map.insert [auto ord: Ord k] (key: k) (value: v) (m: Map k v): Map k v := Map.insertWith (new old => new) key value m

-- One entry.
def Map.singleton [auto ord: Ord k] (key: k) (value: v): Map k v := Map.insert key value Map.empty

-- The value at `key`, if there is one.
def Map.get [auto ord: Ord k] (key: k) (m: Map k v): Maybe v := Map.Tree.get key m.tree

-- The value at `key`, or `d`.
def Map.getOr [auto ord: Ord k] (d: v) (key: k) (m: Map k v): v := Maybe.withDefault d (Map.get key m)

def Map.contains [auto ord: Ord k] (key: k) (m: Map k v): Bool := match Map.get key m with
  | Just _  => True
  | Nothing => False

-- Without `key` (the same map if it isn't there).
def Map.remove [auto ord: Ord k] (key: k) (m: Map k v): Map k v :=
  { tree = Map.Tree.remove key m.tree
  , ordered = Map.Tree.removeWithin key Nothing Nothing m.tree m.ordered
  }

-- The value at `key` changed by `f`, which sees `Nothing` when there's none
-- and removes the entry by returning `Nothing`.
def Map.alter [auto ord: Ord k] (f: Maybe v -> Maybe v) (key: k) (m: Map k v): Map k v :=
  match f (Map.get key m) with
    | Nothing    => Map.remove key m
    | Just value => Map.insert key value m

-- The value at `key` changed by `f`, if there is one.
def Map.adjust [auto ord: Ord k] (f: v -> v) (key: k) (m: Map k v): Map k v :=
  match Map.get key m with
    | Nothing  => m
    | Just old => Map.insert key (f old) m

-- The number of entries, O(1).
def Map.size (m: Map k v [ord := o]): Nat := Map.Tree.size m.tree

def Map.isEmpty (m: Map k v [ord := o]): Bool := Nat.equal (Map.size m) 0

-- The entries, in key order.
def Map.toList (m: Map k v [ord := o]): List (k, v) := Map.Tree.toListOnto m.tree Nil

def Map.keys (m: Map k v [ord := o]): List k := List.map Pair.fst (Map.toList m)

def Map.values (m: Map k v [ord := o]): List v := List.map Pair.snd (Map.toList m)

-- A map of the pairs; a later pair's value replaces an earlier one's.
def Map.fromList [auto ord: Ord k] (xs: List (k, v)): Map k v :=
  List.foldLeft (m (key, value) => Map.insert key value m) Map.empty xs

-- Left fold over the entries in key order: `f (f z k1 v1) k2 v2`.
def Map.foldLeft (f: b -> k -> v -> b) (z: b) (m: Map k v [ord := o]): b := Map.Tree.foldLeft f z m.tree

-- Every value changed by `f`; the keys stay.
def Map.map (f: v -> w) (m: Map k v [ord := o]): Map k w [ord := o] :=
  { tree = Map.Tree.map f m.tree
  , ordered = Map.Tree.mapWithin o f Nothing Nothing m.tree m.ordered
  }

-- The entries for which `p` holds.
def Map.filter [auto ord: Ord k] (p: k -> v -> Bool) (m: Map k v): Map k v :=
  Map.foldLeft (acc key value => if p key value then Map.insert key value acc else acc) Map.empty m

-- Both maps' entries; where both have a key, the first map's value.
def Map.union [auto ord: Ord k] (a: Map k v) (b: Map k v): Map k v :=
  Map.foldLeft (acc key value => Map.insert key value acc) b a

-- What `get` says about `insert`, whatever the map was.

theorem Map.getEmpty [auto ord: Ord k] (key: k): Map.get key (Map.empty: Map k v) = Nothing := rfl

theorem Map.getInsert [auto ord: Ord k] (key: k) (value: v) (m: Map k v):
    (m |> Map.insert key value |> Map.get key) = Just value :=
  Eq.trans (Map.Tree.getInsertWith (new old => new) key value Nothing Nothing m.tree Trivial Trivial m.ordered)
    (Eq.cong Just (Map.Tree.combineFirst value (Map.get key m)))

theorem Map.getInsertOther [auto ord: Ord k] (key: k) (value: v) (other: k) (ne: Not (other = key)) (m: Map k v):
    (m |> Map.insert key value |> Map.get other) = Map.get other m :=
  Map.Tree.getInsertWithOther (new old => new) key value other ne Nothing Nothing m.tree Trivial Trivial m.ordered

theorem Map.getInsertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (m: Map k v):
    Map.get key (Map.insertWith f key value m) = Just (Map.Tree.combine f value (Map.get key m)) :=
  Map.Tree.getInsertWith f key value Nothing Nothing m.tree Trivial Trivial m.ordered

-- `Map.fromList [(1, "a"), (2, "b")]`, in key order, whatever the ordering.
instance Map.instShow [auto showK: Show k] [auto showV: Show v]: Show (Map k v [ord := o]) :=
  Show.fromText (m => Text.append "Map.fromList "
    (Show.list (p => Pair.showWith (x => Show.toSource x) (y => Show.toSource y) p) (Map.toList m)))

def Map.example: Map Nat Text := Map.fromList [(3, "c"), (1, "a"), (2, "b")]

test "map: toList is in key order" := Map.toList Map.example == [(1, "a"), (2, "b"), (3, "c")]
test "map: get" := Map.get 2 Map.example == Just "b" && Map.get 4 Map.example == Nothing
test "map: getOr" := Map.getOr "?" 4 Map.example == "?"
test "map: contains" := Map.contains 1 Map.example && Bool.not (Map.contains 0 Map.example)
test "map: insert replaces" := Map.toList (Map.insert 2 "B" Map.example) == [(1, "a"), (2, "B"), (3, "c")]
test "map: insertWith counts" :=
  Map.toList (List.foldLeft (m c => Map.insertWith Nat.add c 1 m) Map.empty ['b', 'a', 'b']) == [('a', 1), ('b', 2)]
test "map: remove" := Map.toList (Map.remove 2 Map.example) == [(1, "a"), (3, "c")] && Map.size (Map.remove 9 Map.example) == 3
test "map: alter" := Map.toList (Map.alter (old => Nothing) 1 (Map.alter (old => Just "d") 4 Map.example)) == [(2, "b"), (3, "c"), (4, "d")]
test "map: adjust" := Map.get 3 (Map.adjust (t => Text.append t "!") 3 Map.example) == Just "c!"
test "map: size" := Map.size Map.example == 3 && Map.isEmpty (Map.empty: Map Nat Nat)
test "map: keys and values" := Map.keys Map.example == [1, 2, 3] && Map.values Map.example == ["a", "b", "c"]
test "map: fromList, later wins" := Map.toList (Map.fromList [(1, 1), (1, 2)]) == [(1, 2)]
test "map: foldLeft" := Map.foldLeft (acc key t => acc + key) 0 Map.example == 6
test "map: map" := Map.values (Map.map Text.length Map.example) == [1, 1, 1]
test "map: filter" := Map.keys (Map.filter (key t => Nat.leq 2 key) Map.example) == [2, 3]
test "map: union" := Map.toList (Map.union (Map.singleton 1 "x") Map.example) == [(1, "x"), (2, "b"), (3, "c")]
test "map: show" := "${Map.example}" == "Map.fromList [(1, \"a\"), (2, \"b\"), (3, \"c\")]"
