--| `Map.Raw k v`: the representation of a `Map` (std/Map/Map.sw), a
--| weight-balanced binary search tree (Adams's trees, as in Haskell's
--| `Data.Map`) with the ordering of the keys in the type. The tree carries
--| proofs that its keys are in order (`Map.Tree.Ordered`) and that its stored
--| sizes are right (`Map.Tree.Sized`), erased at run time. Two raw maps with
--| the same entries can be different trees; `Map` is the quotient that
--| identifies them. What each operation does to the entries, `Map.Raw.Equiv`,
--| and the lemmas that each operation respects it are in std/Map/Spec.sw.
--| Insertion, lookup and removal take O(log n) comparisons; `size` is O(1).
-- (docs/proposals/interfaces.md §7.5, D169)
-- (docs/proposals/map-equality.md §8)
-- docs/proposals/map-set.md.

import Std (Eq)
import Map.Tree (Tip, Bin)
import Map.Tree.Shape (Keep, SingleL, DoubleL, SingleR, DoubleR)

--| A balanced binary search tree of keys and values, the representation of a
--| `Map`: each node stores the number of keys under it.
type Map.Tree (k: Type) (v: Type): Type =
  | Tip
  | Bin (size: Nat) (left: Map.Tree k v) (key: k) (value: v) (right: Map.Tree k v)

--| The number of keys in the tree, as stored at its root.
def Map.Tree.size: (tree: Map.Tree k v) → Nat
  | Tip => 0
  | Bin s _ _ _ _ => s

--| A node, with its size worked out.
def Map.Tree.bin (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v): Map.Tree k v :=
  Bin (Succ (Map.Tree.size l + Map.Tree.size r)) l key value r

--| A rotation that rebalances a node, or `Keep` for none. `Map.Tree.shape`
--| picks one from the sizes alone, and `Map.Tree.rebuild` performs it; a
--| rotation that doesn't fit the tree's shape just makes a node.
-- So rebuilding keeps the keys in order whatever the sizes say, and the
-- proofs below never look at them.
type Map.Tree.Shape: Type =
  | Keep
  | SingleL
  | DoubleL
  | SingleR
  | DoubleR

--| A node rotated once to the left: the right child's left subtree moves under the new left node.
def Map.Tree.singleL (l: Map.Tree k v) (key: k) (value: v): (r: Map.Tree k v) → Map.Tree k v
  | Bin _ rl rk rv rr => Map.Tree.bin (Map.Tree.bin l key value rl) rk rv rr
  | Tip => Map.Tree.bin l key value Tip

--| A node rotated twice to the left: the right child's left child becomes the root.
def Map.Tree.doubleL (l: Map.Tree k v) (key: k) (value: v): (r: Map.Tree k v) → Map.Tree k v
  | Bin _ (Bin _ rll rlk rlv rlr) rk rv rr =>
    Map.Tree.bin (Map.Tree.bin l key value rll) rlk rlv (Map.Tree.bin rlr rk rv rr)
  | r => Map.Tree.bin l key value r

--| A node rotated once to the right, the mirror image of `Map.Tree.singleL`.
@[noReceiver]
def Map.Tree.singleR (key: k) (value: v) (r: Map.Tree k v): (l: Map.Tree k v) → Map.Tree k v
  | Bin _ ll lk lv lr => Map.Tree.bin ll lk lv (Map.Tree.bin lr key value r)
  | Tip => Map.Tree.bin Tip key value r

--| A node rotated twice to the right, the mirror image of `Map.Tree.doubleL`.
@[noReceiver]
def Map.Tree.doubleR (key: k) (value: v) (r: Map.Tree k v): (l: Map.Tree k v) → Map.Tree k v
  | Bin _ ll lk lv (Bin _ lrl lrk lrv lrr) =>
    Map.Tree.bin (Map.Tree.bin ll lk lv lrl) lrk lrv (Map.Tree.bin lrr key value r)
  | l => Map.Tree.bin l key value r

--| A node built from its parts with the given rotation.
@[noReceiver]
def Map.Tree.rebuild: (shape: Map.Tree.Shape) → (l: Map.Tree k v) → (key: k) → (value: v) → (r: Map.Tree k v) → Map.Tree k v
  | Keep, l, key, value, r => Map.Tree.bin l key value r
  | SingleL, l, key, value, r => Map.Tree.singleL l key value r
  | DoubleL, l, key, value, r => Map.Tree.doubleL l key value r
  | SingleR, l, key, value, r => Map.Tree.singleR key value r l
  | DoubleR, l, key, value, r => Map.Tree.doubleR key value r l

--| The left rotation for a right-heavy node: single or double, by the sizes of the right child's children.
def Map.Tree.shapeL: (tree: Map.Tree k v) → Map.Tree.Shape
  | Bin _ rl _ _ rr => if Nat.leq (Succ (Map.Tree.size rl)) (Map.Tree.size rr * 2) then SingleL else DoubleL
  | Tip => Keep

--| The right rotation for a left-heavy node: single or double, by the sizes of the left child's children.
def Map.Tree.shapeR: (tree: Map.Tree k v) → Map.Tree.Shape
  | Bin _ ll _ _ lr => if Nat.leq (Succ (Map.Tree.size lr)) (Map.Tree.size ll * 2) then SingleR else DoubleR
  | Tip => Keep

--| A rotation when one side has more than three times the other's keys
--| (Data.Map's delta 3 and ratio 2). With one key or none in all, the
--| rotation picked doesn't fit, so it makes a plain node.
def Map.Tree.shape (l: Map.Tree k v) (r: Map.Tree k v): Map.Tree.Shape :=
  let sizeL := Map.Tree.size l
  let sizeR := Map.Tree.size r
  if Nat.leq (Succ (sizeL * 3)) sizeR then Map.Tree.shapeL r
  else if Nat.leq (Succ (sizeR * 3)) sizeL then Map.Tree.shapeR l
  else Keep

--| A node, rebalanced: `l` and `r` were balanced, and one has changed by at
--| most one key since.
def Map.Tree.balance (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v): Map.Tree k v :=
  Map.Tree.rebuild (Map.Tree.shape l r) l key value r

-- Operations on trees

--| `value` at `key`; if `key` is there already, `f value old`.
@[noReceiver]
def Map.Tree.insertWith [auto ord: Ord k] (f: v → v → v) (key: k) (value: v): (tree: Map.Tree k v) → Map.Tree k v
  | Tip => Bin 1 Tip key value Tip
  | Bin s l kk vv r => match Ord.compare key kk with
    | Less => Map.Tree.balance (Map.Tree.insertWith f key value l) kk vv r
    | Equal => Bin s l kk (f value vv) r
    | Greater => Map.Tree.balance l kk vv (Map.Tree.insertWith f key value r)

--| The value at `key` in the tree, if there is one, found by comparing down one path.
@[noReceiver]
@[tailrec]
def Map.Tree.get [auto ord: Ord k] (key: k): (tree: Map.Tree k v) → Option v
  | Tip => None
  | Bin _ l kk vv r => match Ord.compare key kk with
    | Less => Map.Tree.get key l
    | Equal => Some vv
    | Greater => Map.Tree.get key r

--| The smallest key of a node whose key is `key` and whose left subtree is
--| the tree given, and its value.
@[noReceiver]
@[tailrec]
def Map.Tree.minKey (key: k): (tree: Map.Tree k v) → k
  | Tip => key
  | Bin _ l lk _ _ => Map.Tree.minKey lk l

--| The value at the smallest key of the tree, or `value` for an empty tree.
@[noReceiver]
@[tailrec]
def Map.Tree.minValue (value: v): (tree: Map.Tree k v) → v
  | Tip => value
  | Bin _ l _ lv _ => Map.Tree.minValue lv l

--| The node `l key value r` without its smallest key.
def Map.Tree.deleteMin: (l: Map.Tree k v) → (key: k) → (value: v) → (r: Map.Tree k v) → Map.Tree k v
  | Tip, key, value, r => r
  | Bin _ ll lk lv lr, key, value, r => Map.Tree.balance (Map.Tree.deleteMin ll lk lv lr) key value r

--| The node `l key value r`'s smallest entry and the node without it, in one
--| walk down the left spine (`minKey`, `minValue` and `deleteMin` together).
def Map.Tree.minView: (l: Map.Tree k v) → (key: k) → (value: v) → (r: Map.Tree k v) → ((k, v), Map.Tree k v)
  | Tip, key, value, r => ((key, value), r)
  | Bin _ ll lk lv lr, key, value, r =>
    let (smallest, rest) := Map.Tree.minView ll lk lv lr
    (smallest, Map.Tree.balance rest key value r)

--| The smallest entry and the tree without it; none for an empty tree.
def Map.Tree.popMin: (tree: Map.Tree k v) → Option ((k, v), Map.Tree k v)
  | Tip => None
  | Bin _ l key value r => Some (Map.Tree.minView l key value r)

--| Two trees, every key of the first below every key of the second, as one.
def Map.Tree.glue: (l: Map.Tree k v) → (r: Map.Tree k v) → Map.Tree k v
  | Tip, r => r
  | l, Tip => l
  | l, Bin _ rl rk rv rr =>
    Map.Tree.balance l (Map.Tree.minKey rk rl) (Map.Tree.minValue rv rl) (Map.Tree.deleteMin rl rk rv rr)

--| The tree without `key`, rebalanced.
@[noReceiver]
def Map.Tree.remove [auto ord: Ord k] (key: k): (tree: Map.Tree k v) → Map.Tree k v
  | Tip => Tip
  | Bin s l kk vv r => match Ord.compare key kk with
    | Less => Map.Tree.balance (Map.Tree.remove key l) kk vv r
    | Equal => Map.Tree.glue l r
    | Greater => Map.Tree.balance l kk vv (Map.Tree.remove key r)

--| The entries in key order, followed by `acc`.
def Map.Tree.toListOnto: (tree: Map.Tree k v) → (acc: List (k, v)) → List (k, v)
  | Tip, acc => acc
  | Bin _ l kk vv r, acc => Map.Tree.toListOnto l [(kk, vv), ..Map.Tree.toListOnto r acc]

--| Left fold over the tree's entries in key order.
@[noReceiver]
def Map.Tree.foldLeft (f: b → k → v → b): (initial: b) → (tree: Map.Tree k v) → b
  | z, Tip => z
  | z, Bin _ l kk vv r => Map.Tree.foldLeft f (f (Map.Tree.foldLeft f z l) kk vv) r

--| Every value of the tree changed by `f`, in the same shape.
@[noReceiver]
def Map.Tree.map (f: v → w): (tree: Map.Tree k v) → Map.Tree k w
  | Tip => Tip
  | Bin s l kk vv r => Bin s (Map.Tree.map f l) kk (f vv) (Map.Tree.map f r)

--| Every value of the tree changed by `f`, which also sees its key, in the same shape.
@[noReceiver]
def Map.Tree.mapWithKey (f: k → v → w): (tree: Map.Tree k v) → Map.Tree k w
  | Tip => Tip
  | Bin s l kk vv r => Bin s (Map.Tree.mapWithKey f l) kk (f kk vv) (Map.Tree.mapWithKey f r)

--| The entry with the smallest key of the tree, given the entry `(foundKey, foundValue)`
--| to answer if the tree is empty. Key and value travel as two arguments so the pair is
--| built once, at the end, not at every level.
@[noReceiver]
@[tailrec]
def Map.Tree.minFrom (foundKey: k) (foundValue: v): (tree: Map.Tree k v) → (k, v)
  | Tip => (foundKey, foundValue)
  | Bin _ l kk vv r => Map.Tree.minFrom kk vv l

--| The entry with the smallest key of the tree, or `found` for an empty tree.
@[noReceiver]
def Map.Tree.minOr (found: Option (k, v)): (tree: Map.Tree k v) → Option (k, v)
  | Tip => found
  | Bin _ l kk vv r => Some (Map.Tree.minFrom kk vv l)

--| The entry with the largest key of the tree, given the entry `(foundKey, foundValue)`
--| to answer if the tree is empty (see `minFrom`).
@[noReceiver]
@[tailrec]
def Map.Tree.maxFrom (foundKey: k) (foundValue: v): (tree: Map.Tree k v) → (k, v)
  | Tip => (foundKey, foundValue)
  | Bin _ l kk vv r => Map.Tree.maxFrom kk vv r

--| The entry with the largest key of the tree, or `found` for an empty tree.
@[noReceiver]
def Map.Tree.maxOr (found: Option (k, v)): (tree: Map.Tree k v) → Option (k, v)
  | Tip => found
  | Bin _ l kk vv r => Some (Map.Tree.maxFrom kk vv r)

--| The entry with the largest key below `key` in the tree, or `found` if there is none.
@[noReceiver]
@[tailrec]
def Map.Tree.nearestBelow [auto ord: Ord k] (key: k) (found: Option (k, v)): (tree: Map.Tree k v) → Option (k, v)
  | Tip => found
  | Bin _ l kk vv r => match Ord.compare kk key with
    | Less => Map.Tree.nearestBelow key (Some (kk, vv)) r
    | _ => Map.Tree.nearestBelow key found l

--| The entry with the smallest key above `key` in the tree, or `found` if there is none.
@[noReceiver]
@[tailrec]
def Map.Tree.nearestAbove [auto ord: Ord k] (key: k) (found: Option (k, v)): (tree: Map.Tree k v) → Option (k, v)
  | Tip => found
  | Bin _ l kk vv r => match Ord.compare key kk with
    | Less => Map.Tree.nearestAbove key (Some (kk, vv)) l
    | _ => Map.Tree.nearestAbove key found r

-- Keys in order

--| `x` is above the lower bound: `lo < x`, where no bound is below everything.
def Map.Tree.Above (ord: Ord k): (bound: Option k) → (x: k) → Prop
  | None, x => Unit
  | Some lo, x => Ord.compare lo x = Less

--| `x` is below the upper bound: `x < hi`, where no bound is above everything.
def Map.Tree.Below (ord: Ord k) (x: k): (bound: Option k) → Prop
  | None => Unit
  | Some hi => Ord.compare x hi = Less

--| Every key is strictly between the bounds, and in order: a binary search tree.
@[noReceiver]
def Map.Tree.Within (ord: Ord k): (low: Option k) → (high: Option k) → (tree: Map.Tree k v) → Prop
  | lo, hi, Tip => Unit
  | lo, hi, Bin _ l kk _ r =>
    ((Map.Tree.Above ord lo kk) ∧ (Map.Tree.Below ord kk hi)) ∧ ((Map.Tree.Within ord lo (Some kk) l) ∧ (Map.Tree.Within ord (Some kk) hi r))

--| The keys are in order by `ord`.
@[noReceiver]
def Map.Tree.Ordered (ord: Ord k) (t: Map.Tree k v): Prop := Map.Tree.Within ord None None t

--| Each node's stored size is the number of keys under it, so `size` counts
--| the entries. Rebalancing reads the sizes, but `get`, `toList` and the
--| rest never depend on them; `Map.size` does.
def Map.Tree.Sized: (tree: Map.Tree k v) → Prop
  | Tip => Unit
  | Bin s l _ _ r => (s = Succ (Map.Tree.size l + Map.Tree.size r)) ∧ ((Map.Tree.Sized l) ∧ (Map.Tree.Sized r))

--| A raw map: a tree, the proof that its keys are in order, and the proof
--| that its stored sizes are right (both erased at run time).
type Map.Raw (k: Type) (v: Type) [auto ord: Ord k] = {
  tree: Map.Tree k v,
  ordered: Map.Tree.Ordered ord tree,
  sized: Map.Tree.Sized tree
}

-- Proofs: rebalancing, insertion and removal keep the keys in order.

theorem Map.Tree.aboveTrans (ord: Ord k) (lo: Option k) (a b: k)
    (h: Map.Tree.Above ord lo a) (e: Ord.compare a b = Less): Map.Tree.Above ord lo b := match lo with
      | None => Trivial
      | Some x => ord.trans x a b h e

theorem Map.Tree.belowTrans (ord: Ord k) (hi: Option k) (a b: k)
    (e: Ord.compare a b = Less) (h: Map.Tree.Below ord b hi): Map.Tree.Below ord a hi := match hi with
      | None => Trivial
      | Some y => ord.trans a b y e h

--| `compare y x` is `Less` when `compare x y` is `Greater`.
theorem Map.Tree.lessOfGreater (ord: Ord k) (x: k) (y: k) (e: Ord.compare x y = Greater):
    Ord.compare y x = Less :=
  Eq.trans (ord.flip x y) (Eq.cong Ordering.flip e)

--| `x <= y < z` gives `x < z`.
theorem Map.Tree.lessOfLeLess (ord: Ord k) (x: k) (y: k) (z: k)
    (h: Ord.compare x y ≠ Greater) (e: Ord.compare y z = Less):
    Ord.compare x z = Less := match c: Ord.compare x y with
      | Less => ord.trans x y z c e
      | Equal => rewrite ord.equal x y c in e
      | Greater => Void.exfalso (h rfl)

--| A tree within narrower bounds is within wider ones.
theorem Map.Tree.withinLow (ord: Ord k) (lo: Option k) (a: k) (hi: Option k) (t: Map.Tree k v)
    (h: Map.Tree.Above ord lo a) (w: Map.Tree.Within ord (Some a) hi t): Map.Tree.Within ord lo hi t := match t, w with
      | Tip, w => Trivial
      | Bin _ l kk _ r, Both (Both akk bkk) (Both wl wr) =>
        Both (Both (Map.Tree.aboveTrans ord lo a kk h akk) bkk) (Both (Map.Tree.withinLow ord lo a (Some kk) l h wl) wr)

theorem Map.Tree.withinHigh (ord: Ord k) (lo: Option k) (a: k) (hi: Option k) (t: Map.Tree k v)
    (h: Map.Tree.Below ord a hi) (w: Map.Tree.Within ord lo (Some a) t): Map.Tree.Within ord lo hi t := match t, w with
      | Tip, w => Trivial
      | Bin _ l kk _ r, Both (Both akk bkk) (Both wl wr) =>
        Both (Both akk (Map.Tree.belowTrans ord hi kk a bkk h)) (Both wl (Map.Tree.withinHigh ord (Some kk) a hi r h wr))

theorem Map.Tree.singleLWithin (ord: Ord k) (lo: Option k) (hi: Option k) (l: Map.Tree k v) (key: k) (value: v)
    (ab: Map.Tree.Above ord lo key) (wl: Map.Tree.Within ord lo (Some key) l)
    (r: Map.Tree k v) (be: Map.Tree.Below ord key hi) (wr: Map.Tree.Within ord (Some key) hi r):
    Map.Tree.Within ord lo hi (Map.Tree.singleL l key value r) := match r, wr with
      | Tip, wr => Both (Both ab be) (Both wl wr)
      | Bin _ rl rk rv rr, Both (Both krk brk) (Both wrl wrr) =>
        Both (Both (Map.Tree.aboveTrans ord lo key rk ab krk) brk) (Both (Both (Both ab krk) (Both wl wrl)) wrr)

theorem Map.Tree.doubleLWithin (ord: Ord k) (lo: Option k) (hi: Option k) (l: Map.Tree k v) (key: k) (value: v)
    (ab: Map.Tree.Above ord lo key) (wl: Map.Tree.Within ord lo (Some key) l)
    (r: Map.Tree k v) (be: Map.Tree.Below ord key hi) (wr: Map.Tree.Within ord (Some key) hi r):
    Map.Tree.Within ord lo hi (Map.Tree.doubleL l key value r) := match r, wr with
      | Tip, wr => Both (Both ab be) (Both wl wr)
      | Bin s Tip rk rv rr, wr => Both (Both ab be) (Both wl wr)
      | Bin _ (Bin _ rll rlk rlv rlr) rk rv rr, Both (Both krk brk) (Both (Both (Both krlk rlkrk) (Both wrll wrlr)) wrr) =>
        Both (Both (Map.Tree.aboveTrans ord lo key rlk ab krlk) (Map.Tree.belowTrans ord hi rlk rk rlkrk brk))
          (Both (Both (Both ab krlk) (Both wl wrll)) (Both (Both rlkrk brk) (Both wrlr wrr)))

theorem Map.Tree.singleRWithin (ord: Ord k) (lo: Option k) (hi: Option k) (key: k) (value: v) (r: Map.Tree k v)
    (be: Map.Tree.Below ord key hi) (wr: Map.Tree.Within ord (Some key) hi r)
    (l: Map.Tree k v) (ab: Map.Tree.Above ord lo key) (wl: Map.Tree.Within ord lo (Some key) l):
    Map.Tree.Within ord lo hi (Map.Tree.singleR key value r l) := match l, wl with
      | Tip, wl => Both (Both ab be) (Both wl wr)
      | Bin _ ll lk lv lr, Both (Both alk lkk) (Both wll wlr) =>
        Both (Both alk (Map.Tree.belowTrans ord hi lk key lkk be)) (Both wll (Both (Both lkk be) (Both wlr wr)))

theorem Map.Tree.doubleRWithin (ord: Ord k) (lo: Option k) (hi: Option k) (key: k) (value: v) (r: Map.Tree k v)
    (be: Map.Tree.Below ord key hi) (wr: Map.Tree.Within ord (Some key) hi r)
    (l: Map.Tree k v) (ab: Map.Tree.Above ord lo key) (wl: Map.Tree.Within ord lo (Some key) l):
    Map.Tree.Within ord lo hi (Map.Tree.doubleR key value r l) := match l, wl with
      | Tip, wl => Both (Both ab be) (Both wl wr)
      | Bin s ll lk lv Tip, wl => Both (Both ab be) (Both wl wr)
      | Bin _ ll lk lv (Bin _ lrl lrk lrv lrr), Both (Both alk lkk) (Both wll (Both (Both lklrk lrkk) (Both wlrl wlrr))) =>
        Both (Both (Map.Tree.aboveTrans ord lo lk lrk alk lklrk) (Map.Tree.belowTrans ord hi lrk key lrkk be))
          (Both (Both (Both alk lklrk) (Both wll wlrl)) (Both (Both lrkk be) (Both wlrr wr)))

--| Rebuilding keeps the keys in order, whichever rotation is chosen.
theorem Map.Tree.rebuildWithin (ord: Ord k) (lo: Option k) (hi: Option k) (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi)
    (wl: Map.Tree.Within ord lo (Some key) l) (wr: Map.Tree.Within ord (Some key) hi r)
    (s: Map.Tree.Shape): Map.Tree.Within ord lo hi (Map.Tree.rebuild s l key value r) := match s with
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

theorem Map.Tree.insertWithWithin [auto ord: Ord k] (f: v → v → v) (key: k) (value: v)
    (lo hi: Option k) (t: Map.Tree k v)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi) (w: Map.Tree.Within ord lo hi t):
    Map.Tree.Within ord lo hi (Map.Tree.insertWith f key value t) := match t, w with
      | Tip, w => Both (Both ab be) (Both Trivial Trivial)
      | Bin s l kk vv r, Both (Both akk bkk) (Both wl wr) =>
        match e: Ord.compare key kk with
          | Less => Map.Tree.balanceWithin ord lo hi (Map.Tree.insertWith f key value l) kk vv r akk bkk
            (Map.Tree.insertWithWithin f key value lo (Some kk) l ab e wl) wr
          | Equal => Both (Both akk bkk) (Both wl wr)
          | Greater => Map.Tree.balanceWithin ord lo hi l kk vv (Map.Tree.insertWith f key value r) akk bkk
            wl (Map.Tree.insertWithWithin f key value (Some kk) hi r (Map.Tree.lessOfGreater ord key kk e) be wr)

--| The smallest key is above whatever the node's key is above, and below
--| whatever it's below.
theorem Map.Tree.minKeyAbove (ord: Ord k) (lo: Option k) (key: k) (l: Map.Tree k v)
    (ab: Map.Tree.Above ord lo key) (w: Map.Tree.Within ord lo (Some key) l): Map.Tree.Above ord lo (Map.Tree.minKey key l) :=
  match l, w with
    | Tip, w => ab
    | Bin _ ll lk _ lr, Both (Both alk lkk) (Both wll wlr) => Map.Tree.minKeyAbove ord lo lk ll alk wll

theorem Map.Tree.minKeyBelow (ord: Ord k) (lo: Option k) (hi: Option k) (key: k) (l: Map.Tree k v)
    (be: Map.Tree.Below ord key hi) (w: Map.Tree.Within ord lo (Some key) l): Map.Tree.Below ord (Map.Tree.minKey key l) hi :=
  match l, w with
    | Tip, w => be
    | Bin _ ll lk _ lr, Both (Both alk lkk) (Both wll wlr) =>
      Map.Tree.minKeyBelow ord lo hi lk ll (Map.Tree.belowTrans ord hi lk key lkk be) wll

theorem Map.Tree.deleteMinWithin (ord: Ord k) (lo: Option k) (hi: Option k)
    (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi)
    (wl: Map.Tree.Within ord lo (Some key) l) (wr: Map.Tree.Within ord (Some key) hi r):
    Map.Tree.Within ord (Some (Map.Tree.minKey key l)) hi (Map.Tree.deleteMin l key value r) := match l, wl with
      | Tip, wl => wr
      | Bin _ ll lk lv lr, Both (Both alk lkk) (Both wll wlr) =>
        Map.Tree.balanceWithin ord (Some (Map.Tree.minKey lk ll)) hi (Map.Tree.deleteMin ll lk lv lr) key value r
          (Map.Tree.minKeyBelow ord lo (Some key) lk ll lkk wll) be
          (Map.Tree.deleteMinWithin ord lo (Some key) ll lk lv lr alk lkk wll wlr) wr

theorem Map.Tree.glueWithin (ord: Ord k) (lo: Option k) (hi: Option k) (key: k)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi)
    (l r: Map.Tree k v)
    (wl: Map.Tree.Within ord lo (Some key) l) (wr: Map.Tree.Within ord (Some key) hi r):
    Map.Tree.Within ord lo hi (Map.Tree.glue l r) := match l, r, wr with
      | Tip, r, wr => Map.Tree.withinLow ord lo key hi r ab wr
      | Bin s ll lk lv lr, Tip, wr => Map.Tree.withinHigh ord lo key hi (Bin s ll lk lv lr) be wl
      | Bin s ll lk lv lr, Bin _ rl rk rv rr, Both (Both krk brk) (Both wrl wrr) =>
        Map.Tree.balanceWithin ord lo hi (Bin s ll lk lv lr) (Map.Tree.minKey rk rl) (Map.Tree.minValue rv rl)
          (Map.Tree.deleteMin rl rk rv rr)
          (Map.Tree.aboveTrans ord lo key (Map.Tree.minKey rk rl) ab (Map.Tree.minKeyAbove ord (Some key) rk rl krk wrl))
          (Map.Tree.minKeyBelow ord (Some key) hi rk rl brk wrl)
          (Map.Tree.withinHigh ord lo key (Some (Map.Tree.minKey rk rl)) (Bin s ll lk lv lr)
            (Map.Tree.minKeyAbove ord (Some key) rk rl krk wrl) wl)
          (Map.Tree.deleteMinWithin ord (Some key) hi rl rk rv rr krk brk wrl wrr)

theorem Map.Tree.removeWithin [auto ord: Ord k] (key: k)
    (lo hi: Option k) (t: Map.Tree k v)
    (w: Map.Tree.Within ord lo hi t): Map.Tree.Within ord lo hi (Map.Tree.remove key t) := match t, w with
      | Tip, w => Trivial
      | Bin s l kk vv r, Both (Both akk bkk) (Both wl wr) =>
        match e: Ord.compare key kk with
          | Less => Map.Tree.balanceWithin ord lo hi (Map.Tree.remove key l) kk vv r akk bkk
            (Map.Tree.removeWithin key lo (Some kk) l wl) wr
          | Equal => Map.Tree.glueWithin ord lo hi kk akk bkk l r wl wr
          | Greater => Map.Tree.balanceWithin ord lo hi l kk vv (Map.Tree.remove key r) akk bkk
            wl (Map.Tree.removeWithin key (Some kk) hi r wr)

--| Changing the values doesn't move the keys.
theorem Map.Tree.mapWithin (ord: Ord k) (f: v → w) (lo hi: Option k) (t: Map.Tree k v)
    (w: Map.Tree.Within ord lo hi t): Map.Tree.Within ord lo hi (Map.Tree.map f t) := match t, w with
      | Tip, w => Trivial
      | Bin s l kk vv r, Both b (Both wl wr) =>
        Both b (Both (Map.Tree.mapWithin ord f lo (Some kk) l wl) (Map.Tree.mapWithin ord f (Some kk) hi r wr))

theorem Map.Tree.mapWithKeyWithin (ord: Ord k) (f: k → v → w) (lo hi: Option k) (t: Map.Tree k v)
    (w: Map.Tree.Within ord lo hi t): Map.Tree.Within ord lo hi (Map.Tree.mapWithKey f t) := match t, w with
      | Tip, w => Trivial
      | Bin s l kk vv r, Both b (Both wl wr) =>
        Both b (Both (Map.Tree.mapWithKeyWithin ord f lo (Some kk) l wl) (Map.Tree.mapWithKeyWithin ord f (Some kk) hi r wr))

-- Proofs: every operation keeps the stored sizes right. `bin` works the
-- size out, and each rotation is built from `bin`s.

theorem Map.Tree.binSized (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (sl: Map.Tree.Sized l) (sr: Map.Tree.Sized r): Map.Tree.Sized (Map.Tree.bin l key value r) :=
  Both rfl (Both sl sr)

theorem Map.Tree.singleLSized (l: Map.Tree k v) (key: k) (value: v) (sl: Map.Tree.Sized l)
    (r: Map.Tree k v) (sr: Map.Tree.Sized r): Map.Tree.Sized (Map.Tree.singleL l key value r) := match r, sr with
      | Tip, sr => Map.Tree.binSized l key value Tip sl sr
      | Bin _ rl rk rv rr, Both e (Both srl srr) =>
        Map.Tree.binSized (Map.Tree.bin l key value rl) rk rv rr (Map.Tree.binSized l key value rl sl srl) srr

theorem Map.Tree.doubleLSized (l: Map.Tree k v) (key: k) (value: v) (sl: Map.Tree.Sized l)
    (r: Map.Tree k v) (sr: Map.Tree.Sized r): Map.Tree.Sized (Map.Tree.doubleL l key value r) := match r, sr with
      | Tip, sr => Map.Tree.binSized l key value Tip sl sr
      | Bin s Tip rk rv rr, sr => Map.Tree.binSized l key value (Bin s Tip rk rv rr) sl sr
      | Bin _ (Bin _ rll rlk rlv rlr) rk rv rr, Both e (Both (Both e2 (Both srll srlr)) srr) =>
        Map.Tree.binSized (Map.Tree.bin l key value rll) rlk rlv (Map.Tree.bin rlr rk rv rr)
          (Map.Tree.binSized l key value rll sl srll) (Map.Tree.binSized rlr rk rv rr srlr srr)

theorem Map.Tree.singleRSized (key: k) (value: v) (r: Map.Tree k v) (sr: Map.Tree.Sized r)
    (l: Map.Tree k v) (sl: Map.Tree.Sized l): Map.Tree.Sized (Map.Tree.singleR key value r l) := match l, sl with
      | Tip, sl => Map.Tree.binSized Tip key value r sl sr
      | Bin _ ll lk lv lr, Both e (Both sll slr) =>
        Map.Tree.binSized ll lk lv (Map.Tree.bin lr key value r) sll (Map.Tree.binSized lr key value r slr sr)

theorem Map.Tree.doubleRSized (key: k) (value: v) (r: Map.Tree k v) (sr: Map.Tree.Sized r)
    (l: Map.Tree k v) (sl: Map.Tree.Sized l): Map.Tree.Sized (Map.Tree.doubleR key value r l) := match l, sl with
      | Tip, sl => Map.Tree.binSized Tip key value r sl sr
      | Bin s ll lk lv Tip, sl => Map.Tree.binSized (Bin s ll lk lv Tip) key value r sl sr
      | Bin _ ll lk lv (Bin _ lrl lrk lrv lrr), Both e (Both sll (Both e2 (Both slrl slrr))) =>
        Map.Tree.binSized (Map.Tree.bin ll lk lv lrl) lrk lrv (Map.Tree.bin lrr key value r)
          (Map.Tree.binSized ll lk lv lrl sll slrl) (Map.Tree.binSized lrr key value r slrr sr)

theorem Map.Tree.rebuildSized (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (sl: Map.Tree.Sized l) (sr: Map.Tree.Sized r)
    (s: Map.Tree.Shape): Map.Tree.Sized (Map.Tree.rebuild s l key value r) := match s with
      | Keep => Map.Tree.binSized l key value r sl sr
      | SingleL => Map.Tree.singleLSized l key value sl r sr
      | DoubleL => Map.Tree.doubleLSized l key value sl r sr
      | SingleR => Map.Tree.singleRSized key value r sr l sl
      | DoubleR => Map.Tree.doubleRSized key value r sr l sl

theorem Map.Tree.balanceSized (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (sl: Map.Tree.Sized l) (sr: Map.Tree.Sized r): Map.Tree.Sized (Map.Tree.balance l key value r) :=
  Map.Tree.rebuildSized l key value r sl sr (Map.Tree.shape l r)

theorem Map.Tree.insertWithSized [auto ord: Ord k] (f: v → v → v) (key: k) (value: v)
    (t: Map.Tree k v) (st: Map.Tree.Sized t): Map.Tree.Sized (Map.Tree.insertWith f key value t) := match t, st with
      | Tip, st => Both rfl (Both Trivial Trivial)
      | Bin s l kk vv r, Both e (Both sl sr) =>
        match c: Ord.compare key kk with
          | Less => Map.Tree.balanceSized (Map.Tree.insertWith f key value l) kk vv r (Map.Tree.insertWithSized f key value l sl) sr
          | Equal => Both e (Both sl sr)
          | Greater => Map.Tree.balanceSized l kk vv (Map.Tree.insertWith f key value r) sl (Map.Tree.insertWithSized f key value r sr)

theorem Map.Tree.deleteMinSized (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v)
    (sl: Map.Tree.Sized l) (sr: Map.Tree.Sized r): Map.Tree.Sized (Map.Tree.deleteMin l key value r) := match l, sl with
      | Tip, sl => sr
      | Bin _ ll lk lv lr, Both e (Both sll slr) =>
        Map.Tree.balanceSized (Map.Tree.deleteMin ll lk lv lr) key value r (Map.Tree.deleteMinSized ll lk lv lr sll slr) sr

--| `minView` is `minKey`, `minValue` and `deleteMin` in one walk.
theorem Map.Tree.minViewSplit (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v):
    Map.Tree.minView l key value r = ((Map.Tree.minKey key l, Map.Tree.minValue value l), Map.Tree.deleteMin l key value r) :=
  match l with
    | Tip => rfl
    | Bin _ ll lk lv lr => rewrite Map.Tree.minViewSplit ll lk lv lr in rfl

--| What `popMin` leaves of a non-empty tree is `deleteMin`'s.
theorem Map.Tree.popMinRest (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v) (s: Nat) (smallest: (k, v)) (rest: Map.Tree k v)
    (found: Map.Tree.popMin (Bin s l key value r) = Some (smallest, rest)): rest = Map.Tree.deleteMin l key value r :=
  Eq.cong Pair.snd (Eq.trans (Eq.sym (Option.someInjective found)) (Map.Tree.minViewSplit l key value r))

--| Taking the smallest entry off keeps the keys in order.
theorem Map.Tree.popMinOrdered (ord: Ord k) (t: Map.Tree k v) (smallest: (k, v)) (rest: Map.Tree k v)
    (w: Map.Tree.Ordered ord t) (found: Map.Tree.popMin t = Some (smallest, rest)): Map.Tree.Ordered ord rest :=
  match t, w with
    | Bin s l key value r, Both (Both ab be) (Both wl wr) =>
      rewrite Map.Tree.popMinRest l key value r s smallest rest found in
        Map.Tree.withinLow ord None (Map.Tree.minKey key l) None (Map.Tree.deleteMin l key value r) Trivial
          (Map.Tree.deleteMinWithin ord None None l key value r ab be wl wr)

--| Taking the smallest entry off keeps the stored sizes right.
theorem Map.Tree.popMinSized (t: Map.Tree k v) (smallest: (k, v)) (rest: Map.Tree k v)
    (st: Map.Tree.Sized t) (found: Map.Tree.popMin t = Some (smallest, rest)): Map.Tree.Sized rest := match t, st with
      | Bin s l key value r, Both e (Both sl sr) =>
        rewrite Map.Tree.popMinRest l key value r s smallest rest found in Map.Tree.deleteMinSized l key value r sl sr

theorem Map.Tree.glueSized (l r: Map.Tree k v)
    (sl: Map.Tree.Sized l) (sr: Map.Tree.Sized r): Map.Tree.Sized (Map.Tree.glue l r) := match l, r, sr with
      | Tip, r, sr => sr
      | Bin s ll lk lv lr, Tip, sr => sl
      | Bin s ll lk lv lr, Bin _ rl rk rv rr, Both e (Both srl srr) =>
        Map.Tree.balanceSized (Bin s ll lk lv lr) (Map.Tree.minKey rk rl) (Map.Tree.minValue rv rl)
          (Map.Tree.deleteMin rl rk rv rr) sl (Map.Tree.deleteMinSized rl rk rv rr srl srr)

theorem Map.Tree.removeSized [auto ord: Ord k] (key: k)
    (t: Map.Tree k v) (st: Map.Tree.Sized t): Map.Tree.Sized (Map.Tree.remove key t) := match t, st with
      | Tip, st => Trivial
      | Bin s l kk vv r, Both e (Both sl sr) =>
        match c: Ord.compare key kk with
          | Less => Map.Tree.balanceSized (Map.Tree.remove key l) kk vv r (Map.Tree.removeSized key l sl) sr
          | Equal => Map.Tree.glueSized l r sl sr
          | Greater => Map.Tree.balanceSized l kk vv (Map.Tree.remove key r) sl (Map.Tree.removeSized key r sr)

theorem Map.Tree.sizeMap (f: v → w) (t: Map.Tree k v): Map.Tree.size (Map.Tree.map f t) = Map.Tree.size t :=
  match t with
    | Tip => rfl
    | Bin s l kk vv r => rfl

theorem Map.Tree.mapSized (f: v → w) (t: Map.Tree k v) (st: Map.Tree.Sized t): Map.Tree.Sized (Map.Tree.map f t) :=
  match t, st with
    | Tip, st => Trivial
    | Bin s l kk vv r, Both e (Both sl sr) =>
      Both (rewrite Map.Tree.sizeMap f l, Map.Tree.sizeMap f r in e)
        (Both (Map.Tree.mapSized f l sl) (Map.Tree.mapSized f r sr))

theorem Map.Tree.sizeMapWithKey (f: k → v → w) (t: Map.Tree k v): Map.Tree.size (Map.Tree.mapWithKey f t) = Map.Tree.size t :=
  match t with
    | Tip => rfl
    | Bin s l kk vv r => rfl

theorem Map.Tree.mapWithKeySized (f: k → v → w) (t: Map.Tree k v) (st: Map.Tree.Sized t): Map.Tree.Sized (Map.Tree.mapWithKey f t) :=
  match t, st with
    | Tip, st => Trivial
    | Bin s l kk vv r, Both e (Both sl sr) =>
      Both (rewrite Map.Tree.sizeMapWithKey f l, Map.Tree.sizeMapWithKey f r in e)
        (Both (Map.Tree.mapWithKeySized f l sl) (Map.Tree.mapWithKeySized f r sr))

-- Proofs: what `get` finds.

--| The value for the first entry with that key.
@[tailrec]
def Map.Tree.lookupList [auto ord: Ord k] (key: k): (entries: List (k, v)) → Option v
  | [] => None
  | [(kk, vv), ..rest] => match Ord.compare key kk with
    | Equal => Some vv
    | _ => Map.Tree.lookupList key rest

--| The first option if it has a value, otherwise the second.
def Map.Tree.orElse: (first: Option v) → (second: Option v) → Option v
  | Some x, m => Some x
  | None, m => m

theorem Map.Tree.orElseNone (m: Option v): Map.Tree.orElse m None = m := match m with
  | Some x => rfl
  | None => rfl

--| No key at or below the lower bound is in the tree.
theorem Map.Tree.getAbsentLow [auto ord: Ord k] (key: k) (lo: k) (hi: Option k) (t: Map.Tree k v)
    (w: Map.Tree.Within ord (Some lo) hi t) (h: Ord.compare key lo ≠ Greater): Map.Tree.get key t = None :=
  match t, w with
    | Tip, w => rfl
    | Bin s l kk vv r, Both (Both a b) (Both wl wr) =>
      match e: Ord.compare key kk with
        | Less => Map.Tree.getAbsentLow key lo (Some kk) l wl h
        | Equal => Void.exfalso (Ordering.equalNotLess (Eq.trans (Eq.sym e) (Map.Tree.lessOfLeLess ord key lo kk h a)))
        | Greater => Void.exfalso (Ordering.greaterNotLess (Eq.trans (Eq.sym e) (Map.Tree.lessOfLeLess ord key lo kk h a)))

--| No key at or above the upper bound is in the tree.
theorem Map.Tree.getAbsentHigh [auto ord: Ord k] (key: k) (lo: Option k) (hi: k) (t: Map.Tree k v)
    (w: Map.Tree.Within ord lo (Some hi) t) (h: Ord.compare key hi ≠ Less): Map.Tree.get key t = None :=
  match t, w with
    | Tip, w => rfl
    | Bin s l kk vv r, Both (Both a b) (Both wl wr) =>
      match e: Ord.compare key kk with
        | Less => Void.exfalso (h (ord.trans key kk hi e b))
        | Equal => Void.exfalso (h (rewrite ord.equal key kk e in b))
        | Greater => Map.Tree.getAbsentHigh key (Some kk) hi r wr h

--| `get` finds what a search of the entries in order finds.
theorem Map.Tree.lookupOnto [auto ord: Ord k] (key: k) (lo hi: Option k) (t: Map.Tree k v) (acc: List (k, v))
    (w: Map.Tree.Within ord lo hi t):
    Map.Tree.lookupList key (Map.Tree.toListOnto t acc) = Map.Tree.orElse (Map.Tree.get key t) (Map.Tree.lookupList key acc) :=
  match t, w with
    | Tip, w => rfl
    | Bin s l kk vv r, Both (Both a b) (Both wl wr) =>
      rewrite Map.Tree.lookupOnto key lo (Some kk) l [(kk, vv), ..Map.Tree.toListOnto r acc] wl in
      match e: Ord.compare key kk with
        | Less =>
          rewrite Map.Tree.lookupOnto key (Some kk) hi r acc wr,
            Map.Tree.getAbsentLow key kk hi r wr (x => Ordering.lessNotGreater (Eq.trans (Eq.sym e) x)) in rfl
        | Equal => rewrite Map.Tree.getAbsentHigh key lo kk l wl (x => Ordering.equalNotLess (Eq.trans (Eq.sym e) x)) in rfl
        | Greater =>
          rewrite Map.Tree.getAbsentHigh key lo kk l wl (x => Ordering.greaterNotLess (Eq.trans (Eq.sym e) x)),
            Map.Tree.lookupOnto key (Some kk) hi r acc wr in rfl

theorem Map.Tree.getLookup [auto ord: Ord k] (key: k) (lo: Option k) (hi: Option k) (t: Map.Tree k v)
    (w: Map.Tree.Within ord lo hi t): Map.Tree.get key t = Map.Tree.lookupList key (Map.Tree.toListOnto t []) :=
  Eq.sym (Eq.trans (Map.Tree.lookupOnto key lo hi t [] w) (Map.Tree.orElseNone (Map.Tree.get key t)))

--| Rotations keep the entries in order.
theorem Map.Tree.rebuildOnto (s: Map.Tree.Shape) (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v) (acc: List (k, v)):
    Map.Tree.toListOnto (Map.Tree.rebuild s l key value r) acc = Map.Tree.toListOnto (Map.Tree.bin l key value r) acc :=
  match s, l, r with
    | Keep, l, r => rfl
    | SingleL, l, Tip => rfl
    | SingleL, l, Bin _ rl rk rv rr => rfl
    | DoubleL, l, Tip => rfl
    | DoubleL, l, Bin _ Tip rk rv rr => rfl
    | DoubleL, l, Bin _ (Bin _ rll rlk rlv rlr) rk rv rr => rfl
    | SingleR, Tip, r => rfl
    | SingleR, Bin _ ll lk lv lr, r => rfl
    | DoubleR, Tip, r => rfl
    | DoubleR, Bin _ ll lk lv Tip, r => rfl
    | DoubleR, Bin _ ll lk lv (Bin _ lrl lrk lrv lrr), r => rfl

--| `get` on a rebalanced node is `get` on the node.
theorem Map.Tree.getBalance [auto ord: Ord k] (key: k) (lo: Option k) (hi: Option k)
    (l: Map.Tree k v) (kk: k) (vv: v) (r: Map.Tree k v)
    (ab: Map.Tree.Above ord lo kk) (be: Map.Tree.Below ord kk hi)
    (wl: Map.Tree.Within ord lo (Some kk) l) (wr: Map.Tree.Within ord (Some kk) hi r):
    Map.Tree.get key (Map.Tree.balance l kk vv r) = Map.Tree.get key (Map.Tree.bin l kk vv r) :=
  Eq.trans (Map.Tree.getLookup key lo hi (Map.Tree.balance l kk vv r) (Map.Tree.balanceWithin ord lo hi l kk vv r ab be wl wr))
    (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.Tree.rebuildOnto (Map.Tree.shape l r) l kk vv r []))
      (Eq.sym (Map.Tree.getLookup key lo hi (Map.Tree.bin l kk vv r) (Both (Both ab be) (Both wl wr)))))

--| What `insertWith` stores: `value`, or `f value old`.
def Map.Tree.combine (f: v → v → v) (value: v): (old: Option v) → v
  | None => value
  | Some old => f value old

theorem Map.Tree.getInsertWith [auto ord: Ord k] (f: v → v → v) (key: k) (value: v)
    (lo hi: Option k) (t: Map.Tree k v)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi) (w: Map.Tree.Within ord lo hi t):
    Map.Tree.get key (Map.Tree.insertWith f key value t) = Some (Map.Tree.combine f value (Map.Tree.get key t)) :=
  match t, w with
    | Tip, w => rewrite Ord.compareSelf key in rfl
    | Bin s l kk vv r, Both (Both akk bkk) (Both wl wr) =>
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

theorem Map.Tree.getInsertWithOther [auto ord: Ord k] (f: v → v → v) (key: k) (value: v) (other: k)
    (ne: other ≠ key)
    (lo hi: Option k) (t: Map.Tree k v)
    (ab: Map.Tree.Above ord lo key) (be: Map.Tree.Below ord key hi) (w: Map.Tree.Within ord lo hi t):
    Map.Tree.get other (Map.Tree.insertWith f key value t) = Map.Tree.get other t := match t, w with
      | Tip, w =>
        match e: Ord.compare other key with
          | Less => rfl
          | Equal => Void.exfalso (ne (ord.equal other key e))
          | Greater => rfl
      | Bin s l kk vv r, Both (Both akk bkk) (Both wl wr) =>
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

theorem Map.Tree.combineFirst (value: v) (old: Option v): Map.Tree.combine (new o => new) value old = value :=
  match old with
    | None => rfl
    | Some x => rfl

-- Raw maps

--| The raw map with no entries.
def Map.Raw.empty [auto ord: Ord k]: Map.Raw k v := { tree = Tip, ordered = Trivial, sized = Trivial }

--| `value` at `key`; if `key` has a value already, `f value old` (so
--| `Map.insertWith counts key 1 Nat.add` counts).
@[noReceiver]
def Map.Raw.insertWith [auto ord: Ord k] (f: v → v → v) (key: k) (value: v) (m: Map.Raw k v): Map.Raw k v := {
  tree = Map.Tree.insertWith f key value m.tree,
  ordered = Map.Tree.insertWithWithin f key value None None m.tree Trivial Trivial m.ordered,
  sized = Map.Tree.insertWithSized f key value m.tree m.sized
}

--| `value` at `key`, replacing any value there.
@[noReceiver]
def Map.Raw.insert [auto ord: Ord k] (key: k) (value: v) (m: Map.Raw k v): Map.Raw k v := Map.Raw.insertWith (new old => new) key value m

--| The raw map with one entry, `value` at `key`.
def Map.Raw.singleton [auto ord: Ord k] (key: k) (value: v): Map.Raw k v := Map.Raw.insert key value Map.Raw.empty

--| The value at `key`, if there is one.
@[noReceiver]
def Map.Raw.get [auto ord: Ord k] (key: k) (m: Map.Raw k v): Option v := Map.Tree.get key m.tree

--| The value at `key`, or `d`.
def Map.Raw.getOr [auto ord: Ord k] (m: Map.Raw k v) (key: k) (d: v): v := Option.getOrElse (Map.Raw.get key m) d

--| Whether the raw map has an entry at `key`.
@[noReceiver]
def Map.Raw.contains [auto ord: Ord k] (key: k) (m: Map.Raw k v): Bool := match Map.Raw.get key m with
  | Some _ => True
  | None => False

--| Without `key` (the same map if it isn't there).
@[noReceiver]
def Map.Raw.remove [auto ord: Ord k] (key: k) (m: Map.Raw k v): Map.Raw k v := {
  tree = Map.Tree.remove key m.tree,
  ordered = Map.Tree.removeWithin key None None m.tree m.ordered,
  sized = Map.Tree.removeSized key m.tree m.sized
}

--| The value at `key` changed by `f`, which sees `None` when there's none
--| and removes the entry by returning `None`.
@[noReceiver]
def Map.Raw.alter [auto ord: Ord k] (f: Option v → Option v) (key: k) (m: Map.Raw k v): Map.Raw k v :=
  match f (Map.Raw.get key m) with
    | None => Map.Raw.remove key m
    | Some value => Map.Raw.insert key value m

--| The value at `key` changed by `f`, if there is one.
@[noReceiver]
def Map.Raw.adjust [auto ord: Ord k] (f: v → v) (key: k) (m: Map.Raw k v): Map.Raw k v := match Map.Raw.get key m with
  | None => m
  | Some old => Map.Raw.insert key (f old) m

--| The number of entries, O(1).
def Map.Raw.size (m: Map.Raw k v [ord := o]): Nat := Map.Tree.size m.tree

--| Whether the raw map has no entries.
def Map.Raw.isEmpty (m: Map.Raw k v [ord := o]): Bool := Nat.equal (Map.Raw.size m) 0

--| The entries, in key order.
def Map.Raw.toList (m: Map.Raw k v [ord := o]): List (k, v) := Map.Tree.toListOnto m.tree []

--| The keys, in order.
def Map.Raw.keys (m: Map.Raw k v [ord := o]): List k := List.map (Map.Raw.toList m) Pair.fst

--| The values, in the order of their keys.
def Map.Raw.values (m: Map.Raw k v [ord := o]): List v := List.map (Map.Raw.toList m) Pair.snd

--| A map of the pairs; a later pair's value replaces an earlier one's.
def Map.Raw.fromList [auto ord: Ord k] (xs: List (k, v)): Map.Raw k v :=
  List.foldLeft xs Map.Raw.empty (m entry => Map.Raw.insert entry.fst entry.snd m)

--| Left fold over the entries in key order: `f (f z k1 v1) k2 v2`.
@[noReceiver]
def Map.Raw.foldLeft (f: b → k → v → b) (z: b) (m: Map.Raw k v [ord := o]): b := Map.Tree.foldLeft f z m.tree

--| Every value changed by `f`; the keys stay.
@[noReceiver]
def Map.Raw.map (f: v → w) (m: Map.Raw k v [ord := o]): Map.Raw k w [ord := o] := {
  tree = Map.Tree.map f m.tree,
  ordered = Map.Tree.mapWithin o f None None m.tree m.ordered,
  sized = Map.Tree.mapSized f m.tree m.sized
}

--| Every value changed by `f`, which also sees its key; the keys stay.
@[noReceiver]
def Map.Raw.mapWithKey (f: k → v → w) (m: Map.Raw k v [ord := o]): Map.Raw k w [ord := o] := {
  tree = Map.Tree.mapWithKey f m.tree,
  ordered = Map.Tree.mapWithKeyWithin o f None None m.tree m.ordered,
  sized = Map.Tree.mapWithKeySized f m.tree m.sized
}

--| The entry with the smallest key, O(log n).
def Map.Raw.min (m: Map.Raw k v [ord := o]): Option (k, v) := Map.Tree.minOr None m.tree

--| The entry with the largest key, O(log n).
def Map.Raw.max (m: Map.Raw k v [ord := o]): Option (k, v) := Map.Tree.maxOr None m.tree

--| `popMin` given the tree's `popMin` and its equation.
def Map.Raw.popMinFrom (m: Map.Raw k v [ord := o]):
    (popped: Option ((k, v), Map.Tree k v)) → Map.Tree.popMin m.tree = popped → Option ((k, v), Map.Raw k v [ord := o])
  | None, found => None
  | Some (smallest, rest), found =>
    Some (
      smallest,
      {
        tree = rest,
        ordered = Map.Tree.popMinOrdered o m.tree smallest rest m.ordered found,
        sized = Map.Tree.popMinSized m.tree smallest rest m.sized found
      }
    )

--| The smallest entry and the map without it, in one walk.
def Map.Raw.popMin (m: Map.Raw k v [ord := o]): Option ((k, v), Map.Raw k v [ord := o]) :=
  Map.Raw.popMinFrom m (Map.Tree.popMin m.tree) rfl

--| The entry with the largest key below `key` (strictly), O(log n).
@[noReceiver]
def Map.Raw.below [auto ord: Ord k] (key: k) (m: Map.Raw k v): Option (k, v) := Map.Tree.nearestBelow key None m.tree

--| The entry with the smallest key above `key` (strictly), O(log n).
@[noReceiver]
def Map.Raw.above [auto ord: Ord k] (key: k) (m: Map.Raw k v): Option (k, v) := Map.Tree.nearestAbove key None m.tree

-- What `get` says about `insert`, whatever the map was.

theorem Map.Raw.getEmpty [auto ord: Ord k] (key: k): Map.Raw.get key (Map.Raw.empty: Map.Raw k v) = None := rfl

theorem Map.Raw.getInsert [auto ord: Ord k] (key: k) (value: v) (m: Map.Raw k v):
    Map.Raw.get key (Map.Raw.insert key value m) = Some value :=
  Eq.trans (Map.Tree.getInsertWith (new old => new) key value None None m.tree Trivial Trivial m.ordered)
    (Eq.cong Some (Map.Tree.combineFirst value (Map.Raw.get key m)))

theorem Map.Raw.getInsertOther [auto ord: Ord k] (key: k) (value: v) (other: k) (ne: other ≠ key) (m: Map.Raw k v):
    Map.Raw.get other (Map.Raw.insert key value m) = Map.Raw.get other m :=
  Map.Tree.getInsertWithOther (new old => new) key value other ne None None m.tree Trivial Trivial m.ordered

theorem Map.Raw.getInsertWith [auto ord: Ord k] (f: v → v → v) (key: k) (value: v) (m: Map.Raw k v):
    Map.Raw.get key (Map.Raw.insertWith f key value m) = Some (Map.Tree.combine f value (Map.Raw.get key m)) :=
  Map.Tree.getInsertWith f key value None None m.tree Trivial Trivial m.ordered

theorem Map.Raw.getInsertWithOther [auto ord: Ord k] (f: v → v → v) (key: k) (value: v) (other: k) (ne: other ≠ key) (m: Map.Raw k v):
    Map.Raw.get other (Map.Raw.insertWith f key value m) = Map.Raw.get other m :=
  Map.Tree.getInsertWithOther f key value other ne None None m.tree Trivial Trivial m.ordered

--| What `get` says about `map`: it finds what it did, with `f` applied.
-- (The tree's keys stay where they are, so the proof needs no ordering facts.)
theorem Map.Tree.getMap [auto ord: Ord k] (t: Map.Tree k v) (key: k) (f: v → w):
    Map.Tree.get key (Map.Tree.map f t) = Option.map (Map.Tree.get key t) f := match t with
      | Tip => rfl
      | Bin s l kk vv r =>
        match e: Ord.compare key kk with
          | Less => Map.Tree.getMap l key f
          | Equal => rfl
          | Greater => Map.Tree.getMap r key f

theorem Map.Raw.getMap [auto ord: Ord k] (m: Map.Raw k v) (key: k) (f: v → w): Map.Raw.get key (Map.Raw.map f m) = Option.map (Map.Raw.get key m) f :=
  Map.Tree.getMap m.tree key f

theorem Map.Tree.getMapWithKey [auto ord: Ord k] (t: Map.Tree k v) (key: k) (f: k → v → w):
    Map.Tree.get key (Map.Tree.mapWithKey f t) = Option.map (Map.Tree.get key t) (f key) := match t with
      | Tip => rfl
      | Bin s l kk vv r =>
        match e: Ord.compare key kk with
          | Less => Map.Tree.getMapWithKey l key f
          | Equal => rewrite ord.equal key kk e in rfl
          | Greater => Map.Tree.getMapWithKey r key f

theorem Map.Raw.getMapWithKey [auto ord: Ord k] (m: Map.Raw k v) (key: k) (f: k → v → w):
    Map.Raw.get key (Map.Raw.mapWithKey f m) = Option.map (Map.Raw.get key m) (f key) :=
  Map.Tree.getMapWithKey m.tree key f

--| The value of the last pair with that key, which is what `fromList` keeps.
def Map.lookupLast [auto ord: Ord k] (key: k): (entries: List (k, v)) → Option v
  | [] => None
  | [(kk, vv), ..rest] => match Map.lookupLast key rest with
    | Some x => Some x
    | None => match Ord.compare key kk with
      | Equal => Some vv
      | _ => None

--| Adding the pairs to any map: the last pair with the key wins, and if there is none, the map's value stays.
theorem Map.Raw.getFoldInsert [auto ord: Ord k] (m: Map.Raw k v) (key: k) (xs: List (k, v)): Map.Raw.get key (List.foldLeft xs m (acc entry => Map.Raw.insert entry.fst entry.snd acc))
    = Map.Tree.orElse (Map.lookupLast key xs) (Map.Raw.get key m) := match xs with
      | [] => rfl
      | [(kk, vv), ..rest] =>
        rewrite Map.Raw.getFoldInsert (Map.Raw.insert kk vv m) key rest in
        match found: Map.lookupLast key rest with
          | Some x => rfl
          | None =>
            match e: Ord.compare key kk with
              | Less => rewrite Map.Raw.getInsertOther kk vv key (x => Ordering.lessNotEqual (Eq.trans (Eq.sym e) (rewrite x in Ord.compareSelf kk))) m in rfl
              | Equal => rewrite ord.equal key kk e, Map.Raw.getInsert kk vv m in rfl
              | Greater => rewrite Map.Raw.getInsertOther kk vv key (x => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) (rewrite x in Ord.compareSelf kk))) m in rfl

--| What `get` says about `fromList`.
theorem Map.Raw.getFromList [auto ord: Ord k] (key: k) (xs: List (k, v)): Map.Raw.get key (Map.Raw.fromList xs) = Map.lookupLast key xs :=
  Eq.trans (Map.Raw.getFoldInsert Map.Raw.empty key xs) (Map.Tree.orElseNone (Map.lookupLast key xs))

--| A small raw map for the tests below: 1, 2 and 3 to "a", "b" and "c".
def Map.Raw.example: Map.Raw Nat Text := Map.Raw.fromList [(3, "c"), (1, "a"), (2, "b")]

test "raw map: toList is in key order" := Map.Raw.toList Map.Raw.example == [(1, "a"), (2, "b"), (3, "c")]
test "raw map: get" := Map.Raw.get 2 Map.Raw.example == Some "b" ∧ Map.Raw.get 4 Map.Raw.example == None
test "raw map: getOr" := Map.Raw.getOr Map.Raw.example 4 "?" == "?"
test "raw map: contains" := Map.Raw.contains 1 Map.Raw.example ∧ ¬(Map.Raw.contains 0 Map.Raw.example)
test "raw map: insert replaces" := Map.Raw.toList (Map.Raw.insert 2 "B" Map.Raw.example) == [(1, "a"), (2, "B"), (3, "c")]
test "raw map: insertWith counts" :=
  Map.Raw.toList (List.foldLeft ['b', 'a', 'b'] Map.Raw.empty (m c => Map.Raw.insertWith Nat.add c 1 m)) == [('a', 1), ('b', 2)]
test "raw map: remove" := Map.Raw.toList (Map.Raw.remove 2 Map.Raw.example) == [(1, "a"), (3, "c")] ∧ Map.Raw.size (Map.Raw.remove 9 Map.Raw.example) == 3
test "raw map: alter" := Map.Raw.toList (Map.Raw.alter (old => None) 1 (Map.Raw.alter (old => Some "d") 4 Map.Raw.example)) == [(2, "b"), (3, "c"), (4, "d")]
test "raw map: adjust" := Map.Raw.get 3 (Map.Raw.adjust (t => Text.append t "!") 3 Map.Raw.example) == Some "c!"
test "raw map: size" := Map.Raw.size Map.Raw.example == 3 ∧ Map.Raw.isEmpty (Map.Raw.empty: Map.Raw Nat Nat)
test "raw map: keys and values" := Map.Raw.keys Map.Raw.example == [1, 2, 3] ∧ Map.Raw.values Map.Raw.example == ["a", "b", "c"]
test "raw map: fromList, later wins" := Map.Raw.toList (Map.Raw.fromList [(1, 1), (1, 2)]) == [(1, 2)]
test "raw map: foldLeft" := Map.Raw.foldLeft (acc key t => acc + key) 0 Map.Raw.example == 6
test "raw map: map" := Map.Raw.values (Map.Raw.map Text.length Map.Raw.example) == [1, 1, 1]
test "raw map: get after map" := Map.Raw.get 2 (Map.Raw.map Text.length Map.Raw.example) == Some 1 ∧ Map.Raw.get 4 (Map.Raw.map Text.length Map.Raw.example) == None
test "raw map: lookupLast, later wins" := Map.lookupLast 1 [(1, "a"), (2, "b"), (1, "c")] == Some "c" ∧ Map.lookupLast 3 [(1, "a")] == None
