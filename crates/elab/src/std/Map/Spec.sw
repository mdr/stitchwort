-- What each `Map.Raw` operation does to the entries in key order
-- (`Map.Raw.toList`), stated with sorted association lists (`Map.Spec`), and
-- `Map.Raw.Equiv`: two raw maps are equivalent when they have the same
-- entries, whatever their trees' shapes. Each operation respects
-- `Map.Raw.Equiv`, proved from its agreement lemma; that is what lets `Map`
-- (std/Map/Map.sw) lift it to the quotient. `Map.Raw.same` decides it.
-- Stage 0 of docs/proposals/map-equality.md ("Stage 0 results" lists what is
-- and isn't proved).

import Std (Eq)
import Map.Tree (Tip, Bin)

-- Sorted association lists

-- A map's entries in key order, as a list: what the functions below act on.
-- (A type of its own, so that `Map.Spec` belongs to this file, and a dot
-- call such as `xs.filter` on a list doesn't load it.)
type Map.Spec (k: Type) (v: Type) = List (k, v)

-- `value` at `key` in a list sorted by key, as `Map.insertWith` does it:
-- before the first larger key, or combined with the value at an equal key.
def Map.Spec.insertWith [auto ord: Ord k] (f: v → v → v) (key: k) (value: v): List (k, v) → List (k, v)
  | Nil => Cons (key, value) Nil
  | Cons (kk, vv) rest => match Ord.compare key kk with
    | Less => Cons (key, value) (Cons (kk, vv) rest)
    | Equal => Cons (kk, f value vv) rest
    | Greater => Cons (kk, vv) (Map.Spec.insertWith f key value rest)

def Map.Spec.insert [auto ord: Ord k] (key: k) (value: v) (xs: List (k, v)): List (k, v) :=
  Map.Spec.insertWith (new old => new) key value xs

-- Without the entry at `key`.
def Map.Spec.remove [auto ord: Ord k] (key: k): List (k, v) → List (k, v)
  | Nil => Nil
  | Cons (kk, vv) rest => match Ord.compare key kk with
    | Less => Cons (kk, vv) rest
    | Equal => rest
    | Greater => Cons (kk, vv) (Map.Spec.remove key rest)

-- Every value changed by `f`.
def Map.Spec.mapValues (f: v → w): List (k, v) → List (k, w)
  | Nil => Nil
  | Cons (kk, vv) rest => Cons (kk, f vv) (Map.Spec.mapValues f rest)

def Map.Spec.mapWithKey (f: k → v → w): List (k, v) → List (k, w)
  | Nil => Nil
  | Cons (kk, vv) rest => Cons (kk, f kk vv) (Map.Spec.mapWithKey f rest)

-- Left fold over the entries: `f (f z k1 v1) k2 v2`.
def Map.Spec.foldLeft (f: b → k → v → b): b → List (k, v) → b
  | z, Nil => z
  | z, Cons (kk, vv) rest => Map.Spec.foldLeft f (f z kk vv) rest

-- The pairs inserted in turn into an empty list; a later pair wins.
def Map.Spec.fromList [auto ord: Ord k] (xs: List (k, v)): List (k, v) :=
  List.foldLeft xs Nil (l entry => Map.Spec.insert entry.fst entry.snd l)

-- What `Map.filter` does: the entries for which `p` holds, inserted in turn.
def Map.Spec.filter [auto ord: Ord k] (p: k → v → Bool) (xs: List (k, v)): List (k, v) :=
  Map.Spec.foldLeft (l key value => if p key value then Map.Spec.insert key value l else l) Nil xs

-- What `Map.union` does: `a`'s entries inserted into `b`'s, so `a`'s values win.
def Map.Spec.union [auto ord: Ord k] (a: List (k, v)) (b: List (k, v)): List (k, v) :=
  Map.Spec.foldLeft (l key value => Map.Spec.insert key value l) b a

-- What `Map.alter` does.
def Map.Spec.alter [auto ord: Ord k] (f: Option v → Option v) (key: k) (xs: List (k, v)): List (k, v) :=
  match f (Map.Tree.lookupList key xs) with
    | None => Map.Spec.remove key xs
    | Some value => Map.Spec.insert key value xs

-- What `Map.adjust` does.
def Map.Spec.adjust [auto ord: Ord k] (f: v → v) (key: k) (xs: List (k, v)): List (k, v) :=
  match Map.Tree.lookupList key xs with
    | None => xs
    | Some old => Map.Spec.insert key (f old) xs

-- `key` is below the list's first key (or the list is empty).
def Map.Spec.BelowHead (ord: Ord k) (key: k): List (k, v) → Prop
  | Nil => Unit
  | Cons (kk, vv) rest => Ord.compare key kk = Less

-- One step of each, at a smaller, equal or larger first key.

theorem Map.Spec.insertWithLess [auto ord: Ord k] (f: v → v → v) (key: k) (value: v) (kk: k) (vv: v) (rest: List (k, v))
    (e: Ord.compare key kk = Less):
    Map.Spec.insertWith f key value (Cons (kk, vv) rest) = Cons (key, value) (Cons (kk, vv) rest) :=
  rewrite e in rfl

theorem Map.Spec.insertWithEqual [auto ord: Ord k] (f: v → v → v) (key: k) (value: v) (kk: k) (vv: v) (rest: List (k, v))
    (e: Ord.compare key kk = Equal):
    Map.Spec.insertWith f key value (Cons (kk, vv) rest) = Cons (kk, f value vv) rest :=
  rewrite e in rfl

theorem Map.Spec.insertWithGreater [auto ord: Ord k] (f: v → v → v) (key: k) (value: v) (kk: k) (vv: v) (rest: List (k, v))
    (e: Ord.compare key kk = Greater):
    Map.Spec.insertWith f key value (Cons (kk, vv) rest) = Cons (kk, vv) (Map.Spec.insertWith f key value rest) :=
  rewrite e in rfl

theorem Map.Spec.removeLess [auto ord: Ord k] (key: k) (kk: k) (vv: v) (rest: List (k, v))
    (e: Ord.compare key kk = Less):
    Map.Spec.remove key (Cons (kk, vv) rest) = Cons (kk, vv) rest :=
  rewrite e in rfl

theorem Map.Spec.removeEqual [auto ord: Ord k] (key: k) (kk: k) (vv: v) (rest: List (k, v))
    (e: Ord.compare key kk = Equal):
    Map.Spec.remove key (Cons (kk, vv) rest) = rest :=
  rewrite e in rfl

theorem Map.Spec.removeGreater [auto ord: Ord k] (key: k) (kk: k) (vv: v) (rest: List (k, v))
    (e: Ord.compare key kk = Greater):
    Map.Spec.remove key (Cons (kk, vv) rest) = Cons (kk, vv) (Map.Spec.remove key rest) :=
  rewrite e in rfl

-- Trees and their entries

-- Rebalancing doesn't change the entries.
theorem Map.Tree.balanceOnto (l: Map.Tree k v) (key: k) (value: v) (r: Map.Tree k v) (acc: List (k, v)):
    Map.Tree.toListOnto (Map.Tree.balance l key value r) acc = Map.Tree.toListOnto (Map.Tree.bin l key value r) acc :=
  Map.Tree.rebuildOnto (Map.Tree.shape l r) l key value r acc

-- A list operation that passes over every entry below `key` passes over a
-- whole tree whose keys are below `hi`, when `key` isn't below `hi`.
theorem Map.Tree.pastOnto [auto ord: Ord k] (g: List (k, v) → List (k, v)) (key: k)
    (step: (kk: k) → (vv: v) → (rest: List (k, v)) → Ord.compare key kk = Greater → g (Cons (kk, vv) rest) = Cons (kk, vv) (g rest)):
    (lo: Option k) → (hi: k) → (t: Map.Tree k v) → (ys: List (k, v)) →
    Map.Tree.Within ord lo (Some hi) t → Not (Ord.compare key hi = Less) →
    g (Map.Tree.toListOnto t ys) = Map.Tree.toListOnto t (g ys)
  | lo, hi, Tip, ys, w, h => rfl
  | lo, hi, Bin s l kk vv r, ys, Both (Both a b) (Both wl wr), h =>
    match e: Ord.compare key kk with
      | Less => Void.exfalso (h (ord.trans key kk hi e b))
      | Equal => Void.exfalso (h (rewrite ord.equal key kk e in b))
      | Greater =>
        Eq.trans (Map.Tree.pastOnto g key step lo kk l (Cons (kk, vv) (Map.Tree.toListOnto r ys)) wl
            (x => Ordering.greaterNotLess (Eq.trans (Eq.sym e) x)))
          (Eq.cong (zs => Map.Tree.toListOnto l zs)
            (Eq.trans (step kk vv (Map.Tree.toListOnto r ys) e)
              (Eq.cong (zs => Cons (kk, vv) zs) (Map.Tree.pastOnto g key step (Some kk) hi r ys wr h))))

-- Agreement: what each operation does to the entries

theorem Map.Tree.insertWithOnto [auto ord: Ord k] (f: v → v → v) (key: k) (value: v):
    (lo: Option k) → (hi: Option k) → (t: Map.Tree k v) → (acc: List (k, v)) →
    Map.Tree.Within ord lo hi t → Map.Spec.BelowHead ord key acc →
    Map.Tree.toListOnto (Map.Tree.insertWith f key value t) acc = Map.Spec.insertWith f key value (Map.Tree.toListOnto t acc)
  | lo, hi, Tip, Nil, w, bh => rfl
  | lo, hi, Tip, Cons (a, x) rest, w, bh => Eq.sym (Map.Spec.insertWithLess f key value a x rest bh)
  | lo, hi, Bin s l kk vv r, acc, Both (Both akk bkk) (Both wl wr), bh =>
    match e: Ord.compare key kk with
      | Less =>
        Eq.trans (Map.Tree.balanceOnto (Map.Tree.insertWith f key value l) kk vv r acc)
          (Map.Tree.insertWithOnto f key value lo (Some kk) l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl e)
      | Equal =>
        Eq.sym (Eq.trans
          (Map.Tree.pastOnto (Map.Spec.insertWith f key value) key (Map.Spec.insertWithGreater f key value)
            lo kk l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl (x => Ordering.equalNotLess (Eq.trans (Eq.sym e) x)))
          (Eq.cong (zs => Map.Tree.toListOnto l zs) (Map.Spec.insertWithEqual f key value kk vv (Map.Tree.toListOnto r acc) e)))
      | Greater =>
        Eq.trans (Map.Tree.balanceOnto l kk vv (Map.Tree.insertWith f key value r) acc)
          (Eq.trans (Eq.cong (zs => Map.Tree.toListOnto l (Cons (kk, vv) zs))
              (Map.Tree.insertWithOnto f key value (Some kk) hi r acc wr bh))
            (Eq.trans (Eq.cong (zs => Map.Tree.toListOnto l zs)
                (Eq.sym (Map.Spec.insertWithGreater f key value kk vv (Map.Tree.toListOnto r acc) e)))
              (Eq.sym (Map.Tree.pastOnto (Map.Spec.insertWith f key value) key (Map.Spec.insertWithGreater f key value)
                lo kk l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl (x => Ordering.greaterNotLess (Eq.trans (Eq.sym e) x))))))

-- Taking the smallest entry off a node leaves the rest in order.
theorem Map.Tree.deleteMinOnto: (l: Map.Tree k v) → (key: k) → (value: v) → (r: Map.Tree k v) → (acc: List (k, v)) →
    Cons (Map.Tree.minKey key l, Map.Tree.minValue value l) (Map.Tree.toListOnto (Map.Tree.deleteMin l key value r) acc)
      = Map.Tree.toListOnto l (Cons (key, value) (Map.Tree.toListOnto r acc))
  | Tip, key, value, r, acc => rfl
  | Bin s ll lk lv lr, key, value, r, acc =>
    Eq.trans (Eq.cong (zs => Cons (Map.Tree.minKey lk ll, Map.Tree.minValue lv ll) zs)
        (Map.Tree.balanceOnto (Map.Tree.deleteMin ll lk lv lr) key value r acc))
      (Map.Tree.deleteMinOnto ll lk lv lr (Cons (key, value) (Map.Tree.toListOnto r acc)))

theorem Map.Tree.glueOnto: (l: Map.Tree k v) → (r: Map.Tree k v) → (acc: List (k, v)) →
    Map.Tree.toListOnto (Map.Tree.glue l r) acc = Map.Tree.toListOnto l (Map.Tree.toListOnto r acc)
  | Tip, r, acc => rfl
  | Bin s ll lk lv lr, Tip, acc => rfl
  | Bin s ll lk lv lr, Bin s2 rl rk rv rr, acc =>
    Eq.trans (Map.Tree.balanceOnto (Bin s ll lk lv lr) (Map.Tree.minKey rk rl) (Map.Tree.minValue rv rl) (Map.Tree.deleteMin rl rk rv rr) acc)
      (Eq.cong (zs => Map.Tree.toListOnto (Bin s ll lk lv lr) zs) (Map.Tree.deleteMinOnto rl rk rv rr acc))

theorem Map.Tree.removeOnto [auto ord: Ord k] (key: k):
    (lo: Option k) → (hi: Option k) → (t: Map.Tree k v) → (acc: List (k, v)) →
    Map.Tree.Within ord lo hi t → Map.Spec.BelowHead ord key acc →
    Map.Tree.toListOnto (Map.Tree.remove key t) acc = Map.Spec.remove key (Map.Tree.toListOnto t acc)
  | lo, hi, Tip, Nil, w, bh => rfl
  | lo, hi, Tip, Cons (a, x) rest, w, bh => Eq.sym (Map.Spec.removeLess key a x rest bh)
  | lo, hi, Bin s l kk vv r, acc, Both (Both akk bkk) (Both wl wr), bh =>
    match e: Ord.compare key kk with
      | Less =>
        Eq.trans (Map.Tree.balanceOnto (Map.Tree.remove key l) kk vv r acc)
          (Map.Tree.removeOnto key lo (Some kk) l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl e)
      | Equal =>
        Eq.trans (Map.Tree.glueOnto l r acc)
          (Eq.sym (Eq.trans
            (Map.Tree.pastOnto (Map.Spec.remove key) key (Map.Spec.removeGreater key)
              lo kk l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl (x => Ordering.equalNotLess (Eq.trans (Eq.sym e) x)))
            (Eq.cong (zs => Map.Tree.toListOnto l zs) (Map.Spec.removeEqual key kk vv (Map.Tree.toListOnto r acc) e))))
      | Greater =>
        Eq.trans (Map.Tree.balanceOnto l kk vv (Map.Tree.remove key r) acc)
          (Eq.trans (Eq.cong (zs => Map.Tree.toListOnto l (Cons (kk, vv) zs))
              (Map.Tree.removeOnto key (Some kk) hi r acc wr bh))
            (Eq.trans (Eq.cong (zs => Map.Tree.toListOnto l zs)
                (Eq.sym (Map.Spec.removeGreater key kk vv (Map.Tree.toListOnto r acc) e)))
              (Eq.sym (Map.Tree.pastOnto (Map.Spec.remove key) key (Map.Spec.removeGreater key)
                lo kk l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl (x => Ordering.greaterNotLess (Eq.trans (Eq.sym e) x))))))

theorem Map.Tree.mapOnto (f: v → w): (t: Map.Tree k v) → (acc: List (k, v)) →
    Map.Tree.toListOnto (Map.Tree.map f t) (Map.Spec.mapValues f acc) = Map.Spec.mapValues f (Map.Tree.toListOnto t acc)
  | Tip, acc => rfl
  | Bin s l kk vv r, acc =>
    Eq.trans (Eq.cong (zs => Map.Tree.toListOnto (Map.Tree.map f l) (Cons (kk, f vv) zs)) (Map.Tree.mapOnto f r acc))
      (Map.Tree.mapOnto f l (Cons (kk, vv) (Map.Tree.toListOnto r acc)))

theorem Map.Tree.mapWithKeyOnto (f: k → v → w): (t: Map.Tree k v) → (acc: List (k, v)) →
    Map.Tree.toListOnto (Map.Tree.mapWithKey f t) (Map.Spec.mapWithKey f acc) = Map.Spec.mapWithKey f (Map.Tree.toListOnto t acc)
  | Tip, acc => rfl
  | Bin s l kk vv r, acc =>
    Eq.trans (Eq.cong (zs => Map.Tree.toListOnto (Map.Tree.mapWithKey f l) (Cons (kk, f kk vv) zs)) (Map.Tree.mapWithKeyOnto f r acc))
      (Map.Tree.mapWithKeyOnto f l (Cons (kk, vv) (Map.Tree.toListOnto r acc)))

theorem Map.Tree.foldLeftOnto (f: b → k → v → b): (z: b) → (t: Map.Tree k v) → (acc: List (k, v)) →
    Map.Spec.foldLeft f z (Map.Tree.toListOnto t acc) = Map.Spec.foldLeft f (Map.Tree.foldLeft f z t) acc
  | z, Tip, acc => rfl
  | z, Bin s l kk vv r, acc =>
    Eq.trans (Map.Tree.foldLeftOnto f z l (Cons (kk, vv) (Map.Tree.toListOnto r acc)))
      (Map.Tree.foldLeftOnto f (f (Map.Tree.foldLeft f z l) kk vv) r acc)

-- With the stored sizes right, a tree has `size` entries.
theorem Map.Tree.lengthOnto: (t: Map.Tree k v) → (acc: List (k, v)) → Map.Tree.Sized t →
    List.length (Map.Tree.toListOnto t acc) = Map.Tree.size t + List.length acc
  | Tip, acc, st => rfl
  | Bin s l kk vv r, acc, Both e (Both sl sr) =>
    Eq.trans (Map.Tree.lengthOnto l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) sl)
      (Eq.trans (Eq.cong (n => Map.Tree.size l + Succ n) (Map.Tree.lengthOnto r acc sr))
        (Eq.trans (Nat.addSucc (Map.Tree.size l) (Map.Tree.size r + List.length acc))
          (Eq.trans (Eq.cong Succ (Eq.sym (Nat.addAssoc (Map.Tree.size l) (Map.Tree.size r) (List.length acc))))
            (Eq.cong (n => n + List.length acc) (Eq.sym e)))))

-- The same for raw maps.

theorem Map.Raw.toListEmpty [auto ord: Ord k]: Map.Raw.toList (Map.Raw.empty: Map.Raw k v) = Nil := rfl

theorem Map.Raw.toListInsertWith [auto ord: Ord k] (f: v → v → v) (key: k) (value: v) (m: Map.Raw k v):
    Map.Raw.toList (Map.Raw.insertWith f key value m) = Map.Spec.insertWith f key value (Map.Raw.toList m) :=
  Map.Tree.insertWithOnto f key value None None m.tree Nil m.ordered Trivial

theorem Map.Raw.toListInsert [auto ord: Ord k] (key: k) (value: v) (m: Map.Raw k v):
    Map.Raw.toList (Map.Raw.insert key value m) = Map.Spec.insert key value (Map.Raw.toList m) :=
  Map.Raw.toListInsertWith (new old => new) key value m

theorem Map.Raw.toListSingleton [auto ord: Ord k] (key: k) (value: v):
    Map.Raw.toList (Map.Raw.singleton key value: Map.Raw k v) = [(key, value)] := rfl

theorem Map.Raw.toListRemove [auto ord: Ord k] (key: k) (m: Map.Raw k v):
    Map.Raw.toList (Map.Raw.remove key m) = Map.Spec.remove key (Map.Raw.toList m) :=
  Map.Tree.removeOnto key None None m.tree Nil m.ordered Trivial

theorem Map.Raw.toListMap (f: v → w) (m: Map.Raw k v [ord := o]):
    Map.Raw.toList (Map.Raw.map f m) = Map.Spec.mapValues f (Map.Raw.toList m) :=
  Map.Tree.mapOnto f m.tree Nil

theorem Map.Raw.toListMapWithKey (f: k → v → w) (m: Map.Raw k v [ord := o]):
    Map.Raw.toList (Map.Raw.mapWithKey f m) = Map.Spec.mapWithKey f (Map.Raw.toList m) :=
  Map.Tree.mapWithKeyOnto f m.tree Nil

theorem Map.Raw.foldLeftToList (f: b → k → v → b) (z: b) (m: Map.Raw k v [ord := o]):
    Map.Raw.foldLeft f z m = Map.Spec.foldLeft f z (Map.Raw.toList m) :=
  Eq.sym (Map.Tree.foldLeftOnto f z m.tree Nil)

theorem Map.Raw.getToList [auto ord: Ord k] (key: k) (m: Map.Raw k v):
    Map.Raw.get key m = Map.Tree.lookupList key (Map.Raw.toList m) :=
  Map.Tree.getLookup key None None m.tree m.ordered

theorem Map.Raw.sizeToList (m: Map.Raw k v [ord := o]): Map.Raw.size m = List.length (Map.Raw.toList m) :=
  Eq.sym (Eq.trans (Map.Tree.lengthOnto m.tree Nil m.sized) (Nat.addZero (Map.Tree.size m.tree)))

-- A fold whose step agrees with a list step gives the list fold's entries.
theorem Map.Raw.toListFold [auto ord: Ord k] (g: Map.Raw k v → k → v → Map.Raw k v) (h: List (k, v) → k → v → List (k, v))
    (step: (m: Map.Raw k v) → (key: k) → (value: v) → Map.Raw.toList (g m key value) = h (Map.Raw.toList m) key value):
    (m: Map.Raw k v) → (xs: List (k, v)) → Map.Raw.toList (Map.Spec.foldLeft g m xs) = Map.Spec.foldLeft h (Map.Raw.toList m) xs
  | m, Nil => rfl
  | m, Cons (kk, vv) rest =>
    Eq.trans (Map.Raw.toListFold g h step (g m kk vv) rest)
      (Eq.cong (l => Map.Spec.foldLeft h l rest) (step m kk vv))

theorem Map.Raw.toListFromListOnto [auto ord: Ord k]: (m: Map.Raw k v) → (xs: List (k, v)) →
    Map.Raw.toList (List.foldLeft xs m (acc entry => Map.Raw.insert entry.fst entry.snd acc))
      = List.foldLeft xs (Map.Raw.toList m) (l entry => Map.Spec.insert entry.fst entry.snd l)
  | m, Nil => rfl
  | m, Cons (kk, vv) rest =>
    Eq.trans (Map.Raw.toListFromListOnto (Map.Raw.insert kk vv m) rest)
      (Eq.cong (l => List.foldLeft rest l (l2 entry => Map.Spec.insert entry.fst entry.snd l2)) (Map.Raw.toListInsert kk vv m))

theorem Map.Raw.toListFromList [auto ord: Ord k] (xs: List (k, v)):
    Map.Raw.toList (Map.Raw.fromList xs: Map.Raw k v) = Map.Spec.fromList xs :=
  Map.Raw.toListFromListOnto Map.Raw.empty xs

theorem Map.Raw.toListFilterStep [auto ord: Ord k] (p: k → v → Bool) (m: Map.Raw k v) (key: k) (value: v):
    Map.Raw.toList (if p key value then Map.Raw.insert key value m else m)
      = (if p key value then Map.Spec.insert key value (Map.Raw.toList m) else Map.Raw.toList m) :=
  match c: p key value with
    | True => Map.Raw.toListInsert key value m
    | False => rfl

theorem Map.Raw.toListAlter [auto ord: Ord k] (f: Option v → Option v) (key: k) (m: Map.Raw k v):
    Map.Raw.toList (Map.Raw.alter f key m) = Map.Spec.alter f key (Map.Raw.toList m) :=
  rewrite Map.Raw.getToList key m in
  match c: f (Map.Tree.lookupList key (Map.Raw.toList m)) with
    | None => Map.Raw.toListRemove key m
    | Some value => Map.Raw.toListInsert key value m

theorem Map.Raw.toListAdjust [auto ord: Ord k] (f: v → v) (key: k) (m: Map.Raw k v):
    Map.Raw.toList (Map.Raw.adjust f key m) = Map.Spec.adjust f key (Map.Raw.toList m) :=
  rewrite Map.Raw.getToList key m in
  match c: Map.Tree.lookupList key (Map.Raw.toList m) with
    | None => rfl
    | Some old => Map.Raw.toListInsert key (f old) m

-- The entries are in strictly increasing key order

-- Every key is above `lo`, each above the one before.
def Map.Spec.Ascending (ord: Ord k): Option k → List (k, v) → Prop
  | lo, Nil => Unit
  | lo, Cons (kk, vv) rest => And (Map.Tree.Above ord lo kk) (Map.Spec.Ascending ord (Some kk) rest)

def Map.Spec.Sorted (ord: Ord k) (xs: List (k, v)): Prop := Map.Spec.Ascending ord None xs

-- The list can follow keys below `hi`: it's empty, or its first key isn't below `hi`.
def Map.Spec.Fits (ord: Ord k): Option k → List (k, v) → Prop
  | hi, Nil => Unit
  | None, Cons (kk, vv) rest => Void
  | Some h, Cons (kk, vv) rest => Not (Ord.compare kk h = Less)

-- `x < y` and `y <= z` give `x < z`.
theorem Map.Spec.lessOfLessLe (ord: Ord k) (x: k) (y: k) (z: k)
    (e: Ord.compare x y = Less) (h: Not (Ord.compare z y = Less)): Ord.compare x z = Less :=
  match c: Ord.compare y z with
    | Less => ord.trans x y z e c
    | Equal => rewrite Eq.sym (ord.equal y z c) in e
    | Greater => Void.exfalso (h (Map.Tree.lessOfGreater ord y z c))

-- Every key of an ascending list is above its lower bound ...
theorem Map.Spec.keysAbove (ord: Ord k) (key: k): (lo: Option k) → (xs: List (k, v)) → Map.Spec.Ascending ord lo xs →
    List.Mem key (List.map xs Pair.fst) → Map.Tree.Above ord lo key
  | lo, Nil, asc, m => Void.exfalso m
  | lo, Cons (kk, vv) rest, Both above arest, Inl e => rewrite <- e in above
  | None, Cons (kk, vv) rest, Both above arest, Inr m => Trivial
  | Some low, Cons (kk, vv) rest, Both above arest, Inr m => ord.trans low kk key above (Map.Spec.keysAbove ord key (Some kk) rest arest m)

-- ... so its keys don't repeat.
theorem Map.Spec.keysDistinct (ord: Ord k): (lo: Option k) → (xs: List (k, v)) → Map.Spec.Ascending ord lo xs → List.Distinct (List.map xs Pair.fst)
  | lo, Nil, asc => Trivial
  | lo, Cons (kk, vv) rest, Both above arest =>
    Both (m => Ordering.lessNotEqual (Eq.trans (Eq.sym (Map.Spec.keysAbove ord kk (Some kk) rest arest m)) (Ord.compareSelf kk)))
      (Map.Spec.keysDistinct ord (Some kk) rest arest)

theorem Map.Spec.ascendingAbove (ord: Ord k) (lo: Option k) (kk: k): (hi: Option k) → (acc: List (k, v)) →
    Map.Tree.Below ord kk hi → Map.Spec.Ascending ord lo acc → Map.Spec.Fits ord hi acc →
    Map.Spec.Ascending ord (Some kk) acc
  | hi, Nil, b, asc, fits => Trivial
  | None, Cons (a, x) rest, b, asc, fits => Void.exfalso fits
  | Some h, Cons (a, x) rest, b, Both aa arest, fits => Both (Map.Spec.lessOfLessLe ord kk h a b fits) arest

theorem Map.Tree.ascendingOnto (ord: Ord k): (lo: Option k) → (hi: Option k) → (t: Map.Tree k v) → (acc: List (k, v)) →
    Map.Tree.Within ord lo hi t → Map.Spec.Ascending ord lo acc → Map.Spec.Fits ord hi acc →
    Map.Spec.Ascending ord lo (Map.Tree.toListOnto t acc)
  | lo, hi, Tip, acc, w, asc, fits => asc
  | lo, hi, Bin s l kk vv r, acc, Both (Both akk bkk) (Both wl wr), asc, fits =>
    Map.Tree.ascendingOnto ord lo (Some kk) l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl
      (Both akk (Map.Tree.ascendingOnto ord (Some kk) hi r acc wr (Map.Spec.ascendingAbove ord lo kk hi acc bkk asc fits) fits))
      (x => Ordering.equalNotLess (Eq.trans (Eq.sym (Ord.compareSelf kk)) x))

theorem Map.Raw.toListSorted [auto ord: Ord k] (m: Map.Raw k v): Map.Spec.Sorted ord (Map.Raw.toList m) :=
  Map.Tree.ascendingOnto ord None None m.tree Nil m.ordered Trivial Trivial

-- In a list whose keys are all above `lo`, no key at or below `lo` is found.
theorem Map.Spec.lookupBelow [auto ord: Ord k] (key: k): (lo: k) → (xs: List (k, v)) →
    Map.Spec.Ascending ord (Some lo) xs → Not (Ord.compare key lo = Greater) → Map.Tree.lookupList key xs = None
  | lo, Nil, asc, h => rfl
  | lo, Cons (a, x) rest, Both la arest, h =>
    rewrite Map.Tree.lessOfLeLess ord key lo a h la in
    Map.Spec.lookupBelow key a rest arest (z => Ordering.lessNotGreater (Eq.trans (Eq.sym (Map.Tree.lessOfLeLess ord key lo a h la)) z))

theorem Map.Spec.lookupHead [auto ord: Ord k] (key: k) (value: v) (rest: List (k, v)):
    Map.Tree.lookupList key (Cons (key, value) rest) = Some value :=
  rewrite Ord.compareSelf key in rfl

theorem Map.Spec.lookupEqualHead [auto ord: Ord k] (key: k) (kk: k) (vv: v) (rest: List (k, v))
    (e: Ord.compare key kk = Equal): Map.Tree.lookupList key (Cons (kk, vv) rest) = Some vv :=
  rewrite e in rfl

theorem Map.Spec.lookupSkip [auto ord: Ord k] (key: k) (kk: k) (vv: v) (rest: List (k, v))
    (ne: Not (Ord.compare key kk = Equal)): Map.Tree.lookupList key (Cons (kk, vv) rest) = Map.Tree.lookupList key rest :=
  match c: Ord.compare key kk with
    | Less => rfl
    | Equal => Void.exfalso (ne rfl)
    | Greater => rfl

-- A key below the first of a sorted list isn't in it.
theorem Map.Spec.lookupAbsentHead [auto ord: Ord k] (key: k) (kk: k) (vv: v) (rest: List (k, v))
    (e: Ord.compare key kk = Less) (asc: Map.Spec.Ascending ord (Some kk) rest):
    Map.Tree.lookupList key (Cons (kk, vv) rest) = None :=
  Eq.trans (Map.Spec.lookupSkip key kk vv rest (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z)))
    (Map.Spec.lookupBelow key kk rest asc (z => Ordering.lessNotGreater (Eq.trans (Eq.sym e) z)))

-- Two sorted lists with equal first keys that find the same thing
-- everywhere find the same thing in their tails.
theorem Map.Spec.tailsAgree [auto ord: Ord k] (a: k) (x: v) (xs: List (k, v)) (b: k) (y: v) (ys: List (k, v))
    (eab: Ord.compare a b = Equal) (axs: Map.Spec.Ascending ord (Some a) xs) (bys: Map.Spec.Ascending ord (Some b) ys)
    (same: (key: k) → Map.Tree.lookupList key (Cons (a, x) xs) = Map.Tree.lookupList key (Cons (b, y) ys)) (key: k):
    Map.Tree.lookupList key xs = Map.Tree.lookupList key ys :=
  match d: Ord.compare key a with
    | Less =>
      Eq.trans (Map.Spec.lookupBelow key a xs axs (z => Ordering.lessNotGreater (Eq.trans (Eq.sym d) z)))
        (Eq.sym (Map.Spec.lookupBelow key b ys bys
          (z => Ordering.lessNotGreater (Eq.trans (Eq.sym d) (rewrite ord.equal a b eab in z)))))
    | Equal =>
      Eq.trans (Map.Spec.lookupBelow key a xs axs (z => Ordering.equalNotGreater (Eq.trans (Eq.sym d) z)))
        (Eq.sym (Map.Spec.lookupBelow key b ys bys
          (z => Ordering.equalNotGreater (Eq.trans (Eq.sym d) (rewrite ord.equal a b eab in z)))))
    | Greater =>
      Eq.trans (Eq.sym (Map.Spec.lookupSkip key a x xs (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym d) z))))
        (Eq.trans (same key)
          (Map.Spec.lookupSkip key b y ys (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym d) (rewrite ord.equal a b eab in z)))))

-- Sorted lists in which every key finds the same thing are the same list.
theorem Map.Spec.extLookup [auto ord: Ord k]: (lo: Option k) → (xs: List (k, v)) → (ys: List (k, v)) →
    Map.Spec.Ascending ord lo xs → Map.Spec.Ascending ord lo ys →
    ((key: k) → Map.Tree.lookupList key xs = Map.Tree.lookupList key ys) → xs = ys
  | lo, Nil, Nil, ax, ay, same => rfl
  | lo, Nil, Cons (b, y) ys, ax, ay, same =>
    Void.exfalso (Option.noneNotSome y (Eq.trans (same b) (Map.Spec.lookupHead b y ys)))
  | lo, Cons (a, x) xs, Nil, ax, ay, same =>
    Void.exfalso (Option.someNotNone x (Eq.trans (Eq.sym (Map.Spec.lookupHead a x xs)) (same a)))
  | lo, Cons (a, x) xs, Cons (b, y) ys, Both la axs, Both lb bys, same =>
    match c: Ord.compare a b with
      | Less =>
        Void.exfalso (Option.someNotNone x
          (Eq.trans (Eq.sym (Map.Spec.lookupHead a x xs)) (Eq.trans (same a) (Map.Spec.lookupAbsentHead a b y ys c bys))))
      | Equal =>
        rewrite Eq.sym (ord.equal a b c),
          Eq.cong (.getOrElse x)
            (Eq.trans (Eq.sym (Map.Spec.lookupHead a x xs)) (Eq.trans (same a) (Map.Spec.lookupEqualHead a b y ys c))),
          Map.Spec.extLookup (Some a) xs ys axs (rewrite ord.equal a b c in bys) (Map.Spec.tailsAgree a x xs b y ys c axs bys same) in
        rfl
      | Greater =>
        Void.exfalso (Option.noneNotSome y
          (Eq.trans (Eq.sym (Map.Spec.lookupAbsentHead b a x xs (Map.Tree.lessOfGreater ord a b c) axs))
            (Eq.trans (same b) (Map.Spec.lookupHead b y ys))))

-- So `filter` keeps the entries for which `p` holds, in order.

-- In a sorted list, a key is below every later one.
theorem Map.Spec.belowLater [auto ord: Ord k]: (c: k) → (ys: List (k, v)) → (a: k) → (b: v) → (rest: List (k, v)) →
    Map.Spec.Ascending ord (Some c) (List.append ys (Cons (a, b) rest)) → Ord.compare c a = Less
  | c, Nil, a, b, rest, Both ca r => ca
  | c, Cons (e, f) ys2, a, b, rest, Both ce r => ord.trans c e a ce (Map.Spec.belowLater e ys2 a b rest r)

-- Inserting a key above every key of a list puts it at the end.
theorem Map.Spec.insertLast [auto ord: Ord k]: (lo: Option k) → (ys: List (k, v)) → (a: k) → (b: v) → (rest: List (k, v)) →
    Map.Spec.Ascending ord lo (List.append ys (Cons (a, b) rest)) →
    Map.Spec.insert a b ys = List.append ys (Cons (a, b) Nil)
  | lo, Nil, a, b, rest, asc => rfl
  | lo, Cons (c, d) ys2, a, b, rest, Both lc r =>
    Eq.trans (Map.Spec.insertWithGreater (new old => new) a b c d ys2
        (Eq.trans (ord.flip c a) (Eq.cong Ordering.flip (Map.Spec.belowLater c ys2 a b rest r))))
      (Eq.cong (zs => Cons (c, d) zs) (Map.Spec.insertLast (Some c) ys2 a b rest r))

-- Leaving an entry out of a sorted list keeps it sorted.
theorem Map.Spec.ascendingDrop [auto ord: Ord k]: (lo: Option k) → (ys: List (k, v)) → (a: k) → (b: v) → (zs: List (k, v)) →
    Map.Spec.Ascending ord lo (List.append ys (Cons (a, b) zs)) → Map.Spec.Ascending ord lo (List.append ys zs)
  | lo, Nil, a, b, Nil, asc => Trivial
  | lo, Nil, a, b, Cons (c, d) zs2, Both la (Both ac r) => Both (Map.Tree.aboveTrans ord lo a c la ac) r
  | lo, Cons (c, d) ys2, a, b, zs, Both lc r => Both lc (Map.Spec.ascendingDrop (Some c) ys2 a b zs r)

theorem Map.Spec.filterOnto [auto ord: Ord k] (p: k → v → Bool): (ys: List (k, v)) → (xs: List (k, v)) →
    Map.Spec.Ascending ord None (List.append ys xs) →
    Map.Spec.foldLeft (l key value => if p key value then Map.Spec.insert key value l else l) ys xs
      = List.append ys (List.filter xs (e => p e.fst e.snd))
  | ys, Nil, asc => Eq.sym (List.appendNil ys)
  | ys, Cons (a, b) rest, asc =>
    match c: p a b with
      | True =>
        rewrite Map.Spec.insertLast None ys a b rest asc in
        Eq.trans
          (Map.Spec.filterOnto p (List.append ys (Cons (a, b) Nil)) rest
            (rewrite List.appendAssoc ys (Cons (a, b) Nil) rest in asc))
          (List.appendAssoc ys (Cons (a, b) Nil) (List.filter rest (e => p e.fst e.snd)))
      | False => Map.Spec.filterOnto p ys rest (Map.Spec.ascendingDrop None ys a b rest asc)

-- What `get` finds after removing, altering and adjusting

-- `key` isn't `kk` when they compare unequal.
theorem Map.Spec.notEqualOfCompare [auto ord: Ord k] (key: k) (kk: k) (d: Not (Ord.compare key kk = Equal)): Not (key = kk) :=
  e => d (rewrite e in Ord.compareSelf kk)

theorem Map.Spec.lookupRemove [auto ord: Ord k] (key: k): (lo: Option k) → (xs: List (k, v)) → Map.Spec.Ascending ord lo xs →
    Map.Tree.lookupList key (Map.Spec.remove key xs) = None
  | lo, Nil, asc => rfl
  | lo, Cons (kk, vv) rest, Both a arest =>
    match d: Ord.compare key kk with
      | Less => rewrite d in Map.Spec.lookupBelow key kk rest arest (z => Ordering.lessNotGreater (Eq.trans (Eq.sym d) z))
      | Equal => Map.Spec.lookupBelow key kk rest arest (z => Ordering.equalNotGreater (Eq.trans (Eq.sym d) z))
      | Greater => rewrite d in Map.Spec.lookupRemove key (Some kk) rest arest

theorem Map.Spec.lookupRemoveOther [auto ord: Ord k] (key: k) (other: k) (ne: Not (other = key)):
    (xs: List (k, v)) → Map.Tree.lookupList other (Map.Spec.remove key xs) = Map.Tree.lookupList other xs
  | Nil => rfl
  | Cons (kk, vv) rest =>
    match d: Ord.compare key kk with
      | Less => rfl
      | Equal =>
        Eq.sym (Map.Spec.lookupSkip other kk vv rest (z => ne (Eq.trans (ord.equal other kk z) (Eq.sym (ord.equal key kk d)))))
      | Greater =>
        match c: Ord.compare other kk with
          | Equal => rfl
          | Less => Map.Spec.lookupRemoveOther key other ne rest
          | Greater => Map.Spec.lookupRemoveOther key other ne rest

theorem Map.Spec.lookupFilter [auto ord: Ord k] (p: k → v → Bool) (key: k): (lo: Option k) → (xs: List (k, v)) → Map.Spec.Ascending ord lo xs →
    Map.Tree.lookupList key (List.filter xs (e => p e.fst e.snd)) = Option.filter (Map.Tree.lookupList key xs) (p key)
  | lo, Nil, asc => rfl
  | lo, Cons (kk, vv) rest, Both a arest =>
    match d: Ord.compare key kk with
      | Less =>
        match c: p kk vv with
          | True => rewrite d in Map.Spec.lookupFilter p key (Some kk) rest arest
          | False => Map.Spec.lookupFilter p key (Some kk) rest arest
      | Greater =>
        match c: p kk vv with
          | True => rewrite d in Map.Spec.lookupFilter p key (Some kk) rest arest
          | False => Map.Spec.lookupFilter p key (Some kk) rest arest
      | Equal =>
        rewrite ord.equal key kk d in
        match c: p kk vv with
          | True => Map.Spec.lookupHead kk vv _
          | False =>
            rewrite Map.Spec.lookupFilter p kk (Some kk) rest arest,
              Map.Spec.lookupBelow kk kk rest arest (z => Ordering.equalNotGreater (Eq.trans (Eq.sym (Ord.compareSelf kk)) z)) in
            rfl

-- In a sorted list, an entry is there exactly when looking its key up finds
-- its value.
theorem Map.Spec.lookupOfMem [auto ord: Ord k] (key: k) (value: v): (lo: Option k) → (xs: List (k, v)) → Map.Spec.Ascending ord lo xs →
    List.Mem (key, value) xs → Map.Tree.lookupList key xs = Some value
  | lo, Nil, asc, mem => Void.exfalso mem
  | lo, Cons (kk, vv) rest, Both a arest, Inl e => Eq.trans (Eq.cong (x => Map.Tree.lookupList key (Cons x rest)) e) (Map.Spec.lookupHead key value rest)
  | lo, Cons (kk, vv) rest, Both a arest, Inr later =>
    match d: Ord.compare key kk with
      | Equal =>
        Void.exfalso (Option.noneNotSome value
          (Eq.trans (Eq.sym (Map.Spec.lookupBelow key kk rest arest (z => Ordering.equalNotGreater (Eq.trans (Eq.sym d) z))))
            (Map.Spec.lookupOfMem key value (Some kk) rest arest later)))
      | Less => Map.Spec.lookupOfMem key value (Some kk) rest arest later
      | Greater => Map.Spec.lookupOfMem key value (Some kk) rest arest later

theorem Map.Spec.memOfLookup [auto ord: Ord k] (key: k) (value: v): (xs: List (k, v)) →
    Map.Tree.lookupList key xs = Some value → List.Mem (key, value) xs
  | Nil, h => Void.exfalso (Option.noneNotSome value h)
  | Cons (kk, vv) rest, h =>
    match d: Ord.compare key kk with
      | Equal => Inl (rewrite ord.equal key kk d, Eq.cong (.getOrElse vv) h in rfl)
      | Less => Inr (Map.Spec.memOfLookup key value rest h)
      | Greater => Inr (Map.Spec.memOfLookup key value rest h)

-- How many entries inserting and removing leave: inserting a new key adds
-- one, inserting a key that is there adds none; removing a key that is there
-- takes one away, removing one that isn't changes nothing.

theorem Map.Spec.lengthInsertAbsent [auto ord: Ord k] (key: k) (value: v): (xs: List (k, v)) →
    Map.Tree.lookupList key xs = None → List.length (Map.Spec.insert key value xs) = Succ (List.length xs)
  | Nil, h => rfl
  | Cons (kk, vv) rest, h =>
    match d: Ord.compare key kk with
      | Less => rfl
      | Equal => Void.exfalso (Option.someNotNone vv h)
      | Greater => Eq.cong Succ (Map.Spec.lengthInsertAbsent key value rest h)

theorem Map.Spec.lengthInsertPresent [auto ord: Ord k] (key: k) (value: v) (found: v): (lo: Option k) → (xs: List (k, v)) →
    Map.Spec.Ascending ord lo xs → Map.Tree.lookupList key xs = Some found → List.length (Map.Spec.insert key value xs) = List.length xs
  | lo, Nil, asc, h => Void.exfalso (Option.noneNotSome found h)
  | lo, Cons (kk, vv) rest, Both a arest, h =>
    match d: Ord.compare key kk with
      | Less =>
        Void.exfalso (Option.noneNotSome found
          (Eq.trans (Eq.sym (Map.Spec.lookupBelow key kk rest arest (z => Ordering.lessNotGreater (Eq.trans (Eq.sym d) z)))) h))
      | Equal => rfl
      | Greater => Eq.cong Succ (Map.Spec.lengthInsertPresent key value found (Some kk) rest arest h)

theorem Map.Spec.removeAbsent [auto ord: Ord k] (key: k): (xs: List (k, v)) → Map.Tree.lookupList key xs = None → Map.Spec.remove key xs = xs
  | Nil, h => rfl
  | Cons (kk, vv) rest, h =>
    match d: Ord.compare key kk with
      | Less => rfl
      | Equal => Void.exfalso (Option.someNotNone vv h)
      | Greater => Eq.cong (ys => Cons (kk, vv) ys) (Map.Spec.removeAbsent key rest h)

theorem Map.Spec.lengthRemovePresent [auto ord: Ord k] (key: k) (found: v): (lo: Option k) → (xs: List (k, v)) →
    Map.Spec.Ascending ord lo xs → Map.Tree.lookupList key xs = Some found → Succ (List.length (Map.Spec.remove key xs)) = List.length xs
  | lo, Nil, asc, h => Void.exfalso (Option.noneNotSome found h)
  | lo, Cons (kk, vv) rest, Both a arest, h =>
    match d: Ord.compare key kk with
      | Less =>
        Void.exfalso (Option.noneNotSome found
          (Eq.trans (Eq.sym (Map.Spec.lookupBelow key kk rest arest (z => Ordering.lessNotGreater (Eq.trans (Eq.sym d) z)))) h))
      | Equal => rfl
      | Greater => Eq.cong Succ (Map.Spec.lengthRemovePresent key found (Some kk) rest arest h)

theorem Map.Raw.getRemove [auto ord: Ord k] (key: k) (m: Map.Raw k v): Map.Raw.get key (Map.Raw.remove key m) = None :=
  Eq.trans (Map.Raw.getToList key (Map.Raw.remove key m))
    (rewrite Map.Raw.toListRemove key m in Map.Spec.lookupRemove key None (Map.Raw.toList m) (Map.Raw.toListSorted m))

theorem Map.Raw.getRemoveOther [auto ord: Ord k] (key: k) (other: k) (ne: Not (other = key)) (m: Map.Raw k v):
    Map.Raw.get other (Map.Raw.remove key m) = Map.Raw.get other m :=
  Eq.trans (Map.Raw.getToList other (Map.Raw.remove key m))
    (Eq.trans (Eq.cong (Map.Tree.lookupList other) (Map.Raw.toListRemove key m))
      (Eq.trans (Map.Spec.lookupRemoveOther key other ne (Map.Raw.toList m)) (Eq.sym (Map.Raw.getToList other m))))

theorem Map.Raw.getAlter [auto ord: Ord k] (f: Option v → Option v) (key: k) (m: Map.Raw k v):
    Map.Raw.get key (Map.Raw.alter f key m) = f (Map.Raw.get key m) :=
  match c: f (Map.Raw.get key m) with
    | None => Map.Raw.getRemove key m
    | Some value => Map.Raw.getInsert key value m

theorem Map.Raw.getAlterOther [auto ord: Ord k] (f: Option v → Option v) (key: k) (other: k) (ne: Not (other = key)) (m: Map.Raw k v):
    Map.Raw.get other (Map.Raw.alter f key m) = Map.Raw.get other m :=
  match c: f (Map.Raw.get key m) with
    | None => Map.Raw.getRemoveOther key other ne m
    | Some value => Map.Raw.getInsertOther key value other ne m

theorem Map.Raw.getAdjust [auto ord: Ord k] (m: Map.Raw k v) (key: k) (f: v → v):
    Map.Raw.get key (Map.Raw.adjust f key m) = Option.map (Map.Raw.get key m) f :=
  match c: Map.Raw.get key m with
    | None => c
    | Some old => Map.Raw.getInsert key (f old) m

theorem Map.Raw.getAdjustOther [auto ord: Ord k] (f: v → v) (key: k) (other: k) (ne: Not (other = key)) (m: Map.Raw k v):
    Map.Raw.get other (Map.Raw.adjust f key m) = Map.Raw.get other m :=
  match c: Map.Raw.get key m with
    | None => rfl
    | Some old => Map.Raw.getInsertOther key (f old) other ne m

-- The smallest and largest entries, and the nearest below or above a key

def Map.Spec.lastOr (found: Option a): List a → Option a
  | Nil => found
  | Cons x rest => Map.Spec.lastOr (Some x) rest

theorem Map.Spec.lastOrCons: (found: Option a) → (x: a) → (rest: List a) → Map.Spec.lastOr found (Cons x rest) = List.last (Cons x rest)
  | found, x, Nil => rfl
  | found, x, Cons y ys => Map.Spec.lastOrCons (Some x) y ys

theorem Map.Spec.lastOrNone: (xs: List a) → Map.Spec.lastOr None xs = List.last xs
  | Nil => rfl
  | Cons x rest => Map.Spec.lastOrCons None x rest

theorem Map.Tree.minOnto: (t: Map.Tree k v) → (acc: List (k, v)) → List.head (Map.Tree.toListOnto t acc) = Map.Tree.minOr (List.head acc) t
  | Tip, acc => rfl
  | Bin s l kk vv r, acc => Map.Tree.minOnto l (Cons (kk, vv) (Map.Tree.toListOnto r acc))

theorem Map.Tree.maxOnto: (found: Option (k, v)) → (t: Map.Tree k v) → (acc: List (k, v)) →
    Map.Spec.lastOr found (Map.Tree.toListOnto t acc) = Map.Spec.lastOr (Map.Tree.maxOr found t) acc
  | found, Tip, acc => rfl
  | found, Bin s l kk vv r, acc =>
    Eq.trans (Map.Tree.maxOnto found l (Cons (kk, vv) (Map.Tree.toListOnto r acc))) (Map.Tree.maxOnto (Some (kk, vv)) r acc)

theorem Map.Raw.minToList (m: Map.Raw k v [ord := o]): Map.Raw.min m = List.head (Map.Raw.toList m) := Eq.sym (Map.Tree.minOnto m.tree Nil)

-- A list's first element and the rest.
def Map.Spec.uncons: List a → Option (a, List a)
  | Nil => None
  | Cons x rest => Some (x, rest)

-- `popMin` takes the first entry off the entries in key order.
theorem Map.Tree.popMinOnto: (t: Map.Tree k v) →
    Option.map (Map.Tree.popMin t) (view => (view.fst, Map.Tree.toListOnto view.snd Nil)) = Map.Spec.uncons (Map.Tree.toListOnto t Nil)
  | Tip => rfl
  | Bin s l key value r =>
    rewrite Map.Tree.minViewSplit l key value r in Eq.cong Map.Spec.uncons (Map.Tree.deleteMinOnto l key value r Nil)

theorem Map.Raw.popMinFromToList (m: Map.Raw k v [ord := o]):
    (popped: Option ((k, v), Map.Tree k v)) → (found: Map.Tree.popMin m.tree = popped) →
    Option.map (Map.Raw.popMinFrom m popped found) (view => (view.fst, Map.Raw.toList view.snd)) = Map.Spec.uncons (Map.Raw.toList m)
  | None, found =>
    let same: Option.map (Map.Raw.popMinFrom m None found) (view => (view.fst, Map.Raw.toList view.snd))
        = Option.map (Map.Tree.popMin m.tree) (view => (view.fst, Map.Tree.toListOnto view.snd Nil)) := rewrite found in rfl
    Eq.trans same (Map.Tree.popMinOnto m.tree)
  | Some (smallest, rest), found =>
    let same: Option.map (Map.Raw.popMinFrom m (Some (smallest, rest)) found) (view => (view.fst, Map.Raw.toList view.snd))
        = Option.map (Map.Tree.popMin m.tree) (view => (view.fst, Map.Tree.toListOnto view.snd Nil)) := rewrite found in rfl
    Eq.trans same (Map.Tree.popMinOnto m.tree)

theorem Map.Raw.popMinToList (m: Map.Raw k v [ord := o]):
    Option.map (Map.Raw.popMin m) (view => (view.fst, Map.Raw.toList view.snd)) = Map.Spec.uncons (Map.Raw.toList m) :=
  Map.Raw.popMinFromToList m (Map.Tree.popMin m.tree) rfl

theorem Map.Raw.maxToList (m: Map.Raw k v [ord := o]): Map.Raw.max m = List.last (Map.Raw.toList m) :=
  Eq.trans (Eq.sym (Map.Tree.maxOnto None m.tree Nil)) (Map.Spec.lastOrNone (Map.Raw.toList m))

def Map.Spec.isLess [auto ord: Ord k] (a: k) (b: k): Bool := match Ord.compare a b with
  | Less => True
  | _ => False

def Map.Spec.lastBelow [auto ord: Ord k] (key: k) (found: Option (k, v)): List (k, v) → Option (k, v)
  | Nil => found
  | Cons (kk, vv) rest => match Ord.compare kk key with
    | Less => Map.Spec.lastBelow key (Some (kk, vv)) rest
    | _ => Map.Spec.lastBelow key found rest

theorem Map.Spec.lastBelowFilter [auto ord: Ord k] (key: k): (found: Option (k, v)) → (xs: List (k, v)) →
    Map.Spec.lastBelow key found xs = Map.Spec.lastOr found (List.filter xs (e => Map.Spec.isLess e.fst key))
  | found, Nil => rfl
  | found, Cons (kk, vv) rest =>
    match d: Ord.compare kk key with
      | Less => Map.Spec.lastBelowFilter key (Some (kk, vv)) rest
      | Equal => Map.Spec.lastBelowFilter key found rest
      | Greater => Map.Spec.lastBelowFilter key found rest

-- A tree whose keys are all above `lo`, where `lo` isn't below `key`, has no entry below `key`.
theorem Map.Tree.lastBelowPast [auto ord: Ord k] (key: k) (found: Option (k, v)):
    (lo: k) → (hi: Option k) → (t: Map.Tree k v) → (acc: List (k, v)) →
    Map.Tree.Within ord (Some lo) hi t → Not (Ord.compare lo key = Less) →
    Map.Spec.lastBelow key found (Map.Tree.toListOnto t acc) = Map.Spec.lastBelow key found acc
  | lo, hi, Tip, acc, w, h => rfl
  | lo, hi, Bin s l kk vv r, acc, Both (Both akk bkk) (Both wl wr), h =>
    rewrite Map.Tree.lastBelowPast key found lo (Some kk) l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl h in
    match d: Ord.compare kk key with
      | Less => Void.exfalso (h (ord.trans lo kk key akk d))
      | Equal => Map.Tree.lastBelowPast key found kk hi r acc wr (z => Ordering.equalNotLess (Eq.trans (Eq.sym d) z))
      | Greater => Map.Tree.lastBelowPast key found kk hi r acc wr (z => Ordering.greaterNotLess (Eq.trans (Eq.sym d) z))

theorem Map.Tree.belowOnto [auto ord: Ord k] (key: k): (found: Option (k, v)) → (lo: Option k) → (hi: Option k) → (t: Map.Tree k v) → (acc: List (k, v)) →
    Map.Tree.Within ord lo hi t →
    Map.Spec.lastBelow key found (Map.Tree.toListOnto t acc) = Map.Spec.lastBelow key (Map.Tree.nearestBelow key found t) acc
  | found, lo, hi, Tip, acc, w => rfl
  | found, lo, hi, Bin s l kk vv r, acc, Both (Both akk bkk) (Both wl wr) =>
    rewrite Map.Tree.belowOnto key found lo (Some kk) l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl in
    match d: Ord.compare kk key with
      | Less => Map.Tree.belowOnto key (Some (kk, vv)) (Some kk) hi r acc wr
      | Equal => Map.Tree.lastBelowPast key (Map.Tree.nearestBelow key found l) kk hi r acc wr (z => Ordering.equalNotLess (Eq.trans (Eq.sym d) z))
      | Greater => Map.Tree.lastBelowPast key (Map.Tree.nearestBelow key found l) kk hi r acc wr (z => Ordering.greaterNotLess (Eq.trans (Eq.sym d) z))

-- A tree whose keys are all below `hi`, where `key` isn't below `hi`, has no entry above `key`.
theorem Map.Tree.abovePast [auto ord: Ord k] (key: k) (found: Option (k, v)):
    (lo: Option k) → (hi: k) → (t: Map.Tree k v) → Map.Tree.Within ord lo (Some hi) t → Not (Ord.compare key hi = Less) →
    Map.Tree.nearestAbove key found t = found
  | lo, hi, Tip, w, h => rfl
  | lo, hi, Bin s l kk vv r, Both (Both akk bkk) (Both wl wr), h =>
    match d: Ord.compare key kk with
      | Less => Void.exfalso (h (ord.trans key kk hi d bkk))
      | Equal => Map.Tree.abovePast key found (Some kk) hi r wr h
      | Greater => Map.Tree.abovePast key found (Some kk) hi r wr h

theorem Map.Tree.aboveOnto [auto ord: Ord k] (key: k): (lo: Option k) → (hi: Option k) → (t: Map.Tree k v) → (acc: List (k, v)) →
    Map.Tree.Within ord lo hi t →
    List.find (Map.Tree.toListOnto t acc) (e => Map.Spec.isLess key e.fst) = Map.Tree.nearestAbove key (List.find acc (e => Map.Spec.isLess key e.fst)) t
  | lo, hi, Tip, acc, w => rfl
  | lo, hi, Bin s l kk vv r, acc, Both (Both akk bkk) (Both wl wr) =>
    rewrite Map.Tree.aboveOnto key lo (Some kk) l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl in
    match d: Ord.compare key kk with
      | Less => rfl
      | Equal =>
        rewrite Map.Tree.aboveOnto key (Some kk) hi r acc wr in
        Map.Tree.abovePast key _ lo kk l wl (z => Ordering.equalNotLess (Eq.trans (Eq.sym d) z))
      | Greater =>
        rewrite Map.Tree.aboveOnto key (Some kk) hi r acc wr in
        Map.Tree.abovePast key _ lo kk l wl (z => Ordering.greaterNotLess (Eq.trans (Eq.sym d) z))

theorem Map.Raw.belowToList [auto ord: Ord k] (m: Map.Raw k v) (key: k):
    Map.Raw.below key m = List.last (List.filter (Map.Raw.toList m) (e => Map.Spec.isLess e.fst key)) :=
  Eq.trans (Eq.sym (Map.Tree.belowOnto key None None None m.tree Nil m.ordered))
    (Eq.trans (Map.Spec.lastBelowFilter key None (Map.Raw.toList m)) (Map.Spec.lastOrNone (List.filter (Map.Raw.toList m) (e => Map.Spec.isLess e.fst key))))

theorem Map.Raw.aboveToList [auto ord: Ord k] (m: Map.Raw k v) (key: k):
    Map.Raw.above key m = List.find (Map.Raw.toList m) (e => Map.Spec.isLess key e.fst) :=
  Eq.sym (Map.Tree.aboveOnto key None None m.tree Nil m.ordered)

-- What `below` and `above` find, over sorted lists: the nearest key on that
-- side of `key`, with nothing between.

-- `a < b` rules out `b < a`.
theorem Map.Spec.notLessOfLess (ord: Ord k) (a: k) (b: k) (e: Ord.compare a b = Less): Not (Ord.compare b a = Less) :=
  z => Ordering.greaterNotLess (Eq.trans (Eq.sym (Eq.trans (ord.flip a b) (Eq.cong Ordering.flip e))) z)

-- `isLess` is `Less`.
theorem Map.Spec.isLessSound [auto ord: Ord k] (a: k) (b: k) (h: Map.Spec.isLess a b = True): Ord.compare a b = Less :=
  match e: Ord.compare a b with
    | Less => rfl
    | Equal => Void.exfalso (Bool.falseNotTrue h)
    | Greater => Void.exfalso (Bool.falseNotTrue h)

theorem Map.Spec.isLessOf [auto ord: Ord k] (a: k) (b: k) (h: Ord.compare a b = Less): Map.Spec.isLess a b = True :=
  rewrite h in rfl

-- Started with an entry, `lastBelow` finds one.
theorem Map.Spec.lastBelowSomeNotNone [auto ord: Ord k] (key: k): (entry: (k, v)) → (xs: List (k, v)) →
    Not (Map.Spec.lastBelow key (Some entry) xs = None)
  | entry, Nil, h => Option.someNotNone entry h
  | entry, Cons (kk, vv) rest, h =>
    match d: Ord.compare kk key with
      | Less => Map.Spec.lastBelowSomeNotNone key (kk, vv) rest h
      | Equal => Map.Spec.lastBelowSomeNotNone key entry rest h
      | Greater => Map.Spec.lastBelowSomeNotNone key entry rest h

-- `lastBelow` finds what it started with, or an entry of the list below `key`.
theorem Map.Spec.lastBelowFrom [auto ord: Ord k] (key: k): (found: Option (k, v)) → (xs: List (k, v)) → (entry: (k, v)) →
    Map.Spec.lastBelow key found xs = Some entry →
    Or (found = Some entry) (And (List.Mem entry xs) (Ord.compare entry.fst key = Less))
  | found, Nil, entry, h => Inl h
  | found, Cons (kk, vv) rest, entry, h =>
    match d: Ord.compare kk key with
      | Less =>
        match Map.Spec.lastBelowFrom key (Some (kk, vv)) rest entry h with
          | Inl same =>
            let isHead: (kk, vv) = entry := Option.someInjective (kk, vv) entry same
            Inr (Both (Inl isHead) (rewrite <- isHead in d))
          | Inr (Both inRest less) => Inr (Both (Inr inRest) less)
      | Equal =>
        match Map.Spec.lastBelowFrom key found rest entry h with
          | Inl same => Inl same
          | Inr (Both inRest less) => Inr (Both (Inr inRest) less)
      | Greater =>
        match Map.Spec.lastBelowFrom key found rest entry h with
          | Inl same => Inl same
          | Inr (Both inRest less) => Inr (Both (Inr inRest) less)

-- In an ascending list, no key below `key` is above what `lastBelow` finds.
theorem Map.Spec.lastBelowGreatest [auto ord: Ord k] (key: k): (lo: Option k) → (found: Option (k, v)) → (xs: List (k, v)) →
    Map.Spec.Ascending ord lo xs → (entry: (k, v)) → Map.Spec.lastBelow key found xs = Some entry →
    (other: k) → List.Mem other (List.map xs Pair.fst) → Ord.compare other key = Less → Not (Ord.compare entry.fst other = Less)
  | lo, found, Nil, asc, entry, h, other, m, less, wrong => Void.exfalso m
  | lo, found, Cons (kk, vv) rest, Both above arest, entry, h, other, Inl isHead, less, wrong =>
    match d: Ord.compare kk key with
      | Less =>
        match Map.Spec.lastBelowFrom key (Some (kk, vv)) rest entry h with
          | Inl same =>
            let lessSelf: Ord.compare kk kk = Less := rewrite Eq.cong Pair.fst (Eq.sym (Option.someInjective (kk, vv) entry same)), <- isHead at wrong
            Ordering.equalNotLess (Eq.trans (Eq.sym (Ord.compareSelf kk)) lessSelf)
          | Inr (Both inRest below) =>
            Map.Spec.notLessOfLess ord kk entry.fst (Map.Spec.keysAbove ord entry.fst (Some kk) rest arest (List.memMap rest entry inRest Pair.fst))
              (rewrite <- isHead at wrong)
      | Equal => Ordering.equalNotLess (Eq.trans (Eq.sym d) (rewrite <- isHead at less))
      | Greater => Ordering.greaterNotLess (Eq.trans (Eq.sym d) (rewrite <- isHead at less))
  | lo, found, Cons (kk, vv) rest, Both above arest, entry, h, other, Inr inRest, less, wrong =>
    match d: Ord.compare kk key with
      | Less => Map.Spec.lastBelowGreatest key (Some kk) (Some (kk, vv)) rest arest entry h other inRest less wrong
      | Equal => Map.Spec.lastBelowGreatest key (Some kk) found rest arest entry h other inRest less wrong
      | Greater => Map.Spec.lastBelowGreatest key (Some kk) found rest arest entry h other inRest less wrong

-- Finding nothing, `lastBelow` passed no key below `key`.
theorem Map.Spec.lastBelowNone [auto ord: Ord k] (key: k): (found: Option (k, v)) → (xs: List (k, v)) →
    Map.Spec.lastBelow key found xs = None → (other: k) → List.Mem other (List.map xs Pair.fst) → Not (Ord.compare other key = Less)
  | found, Nil, h, other, m, less => Void.exfalso m
  | found, Cons (kk, vv) rest, h, other, Inl isHead, less =>
    match d: Ord.compare kk key with
      | Less => Map.Spec.lastBelowSomeNotNone key (kk, vv) rest h
      | Equal => Ordering.equalNotLess (Eq.trans (Eq.sym d) (rewrite <- isHead at less))
      | Greater => Ordering.greaterNotLess (Eq.trans (Eq.sym d) (rewrite <- isHead at less))
  | found, Cons (kk, vv) rest, h, other, Inr inRest, less =>
    match d: Ord.compare kk key with
      | Less => Map.Spec.lastBelowSomeNotNone key (kk, vv) rest h
      | Equal => Map.Spec.lastBelowNone key found rest h other inRest less
      | Greater => Map.Spec.lastBelowNone key found rest h other inRest less

-- In an ascending list, no key above `key` is below the first entry above it.
theorem Map.Spec.findAboveLeast [auto ord: Ord k] (key: k): (lo: Option k) → (xs: List (k, v)) → Map.Spec.Ascending ord lo xs →
    (entry: (k, v)) → List.find xs (e => Map.Spec.isLess key e.fst) = Some entry →
    (other: k) → List.Mem other (List.map xs Pair.fst) → Ord.compare key other = Less → Not (Ord.compare other entry.fst = Less)
  | lo, Nil, asc, entry, h, other, m, more, wrong => Void.exfalso m
  | lo, Cons (kk, vv) rest, Both above arest, entry, h, other, Inl isHead, more, wrong =>
    match d: Ord.compare key kk with
      | Less =>
        let lessSelf: Ord.compare kk kk = Less := rewrite Eq.cong Pair.fst (Eq.sym (Option.someInjective (kk, vv) entry h)), <- isHead at wrong
        Ordering.equalNotLess (Eq.trans (Eq.sym (Ord.compareSelf kk)) lessSelf)
      | Equal => Ordering.equalNotLess (Eq.trans (Eq.sym d) (rewrite <- isHead at more))
      | Greater => Ordering.greaterNotLess (Eq.trans (Eq.sym d) (rewrite <- isHead at more))
  | lo, Cons (kk, vv) rest, Both above arest, entry, h, other, Inr inRest, more, wrong =>
    match d: Ord.compare key kk with
      | Less =>
        Map.Spec.notLessOfLess ord kk other (Map.Spec.keysAbove ord other (Some kk) rest arest inRest)
          (rewrite Eq.cong Pair.fst (Eq.sym (Option.someInjective (kk, vv) entry h)) at wrong)
      | Equal => Map.Spec.findAboveLeast key (Some kk) rest arest entry h other inRest more wrong
      | Greater => Map.Spec.findAboveLeast key (Some kk) rest arest entry h other inRest more wrong

-- What a fold over the entries leaves at one key (for `Map`'s lemmas)

-- What a fold finds at `key`.
def Map.Spec.atKey (h: v → Option w → Option w): Option v → Option w → Option w
  | None, old => old
  | Some value, old => h value old

theorem Map.Spec.atKeyCombine (f: v → v → v): (x: Option v) → (y: Option v) →
    Map.Spec.atKey (value old => Some (Map.Tree.combine f value old)) x y = Option.merge x y f
  | None, None => rfl
  | None, Some y => rfl
  | Some x, None => rfl
  | Some x, Some y => rfl

theorem Map.Spec.atKeyFirst: (x: Option v) → (y: Option v) → Map.Spec.atKey (value old => Some value) x y = Option.orElse x y
  | None, y => rfl
  | Some x, y => rfl

theorem Map.Spec.atKeyFilterMap (f: v → Option w): (x: Option v) → Map.Spec.atKey (value old => Option.orElse (f value) old) x None = Option.flatMap x f
  | None => rfl
  | Some value => Option.orElseNone (f value)

def Map.Spec.sameKey [auto ord: Ord k] (a: k) (b: k): Bool := match Ord.compare a b with
  | Equal => True
  | _ => False

-- `sameKey` says equal, and is `==` (the `DecEq` in the `Ord`).
theorem Map.Spec.sameKeySound [auto ord: Ord k] (a: k) (b: k) (h: Map.Spec.sameKey a b = True): a = b :=
  match e: Ord.compare a b with
    | Less => Void.exfalso (Bool.falseNotTrue h)
    | Equal => ord.equal a b e
    | Greater => Void.exfalso (Bool.falseNotTrue h)

theorem Map.Spec.sameKeyDecide [auto ord: Ord k] (a: k) (b: k): Map.Spec.sameKey a b = (b == a) :=
  match e: Ord.compare a b with
    | Less =>
      Eq.sym (Decidable.toBoolOfNot (DecEq.decide b a) (q => Map.Spec.notEqualOfCompare a b (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z)) (Eq.sym q)))
    | Equal => Eq.sym (Decidable.toBoolOf (DecEq.decide b a) (Eq.sym (ord.equal a b e)))
    | Greater =>
      Eq.sym (Decidable.toBoolOfNot (DecEq.decide b a) (q => Map.Spec.notEqualOfCompare a b (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z)) (Eq.sym q)))

def Map.Spec.nonEmpty: List a → Option (List a)
  | Nil => None
  | Cons x rest => Some (Cons x rest)

-- Bulk operations, through sorted lists (docs/proposals/maps.md §4.6)
--
-- `union`, `unionWith`, `intersectWith`, `difference`, `filter` and
-- `filterMap` take the entries in key order, combine them in one pass
-- (`Map.Spec.merge`, `Map.Spec.mapMaybe`, `List.filter`), and build a balanced
-- tree from the sorted result in one more (`Map.Raw.fromSorted`): O(n + m).
-- When one map is much smaller than the other, `union`, `unionWith` and
-- `difference` work key by key over the smaller one instead, O(n log m)
-- for its n keys, and so does `intersectWith` when the first map is the
-- smaller (`Map.Raw.isSmall`).

-- `rest`, with `(key, value)` in front if there is a value. (A function of
-- its own, like `List.filterStep`, so the rest is written once.)
def Map.Spec.consEntry (key: k) (rest: List (k, x)): Option x → List (k, x)
  | Some value => Cons (key, value) rest
  | None => rest

-- The entries `f` keeps, with the values it gives; `f` sees each key and value.
def Map.Spec.mapMaybe (f: k → v → Option x): List (k, v) → List (k, x)
  | Nil => Nil
  | Cons (kk, vv) rest => Map.Spec.consEntry kk (Map.Spec.mapMaybe f rest) (f kk vv)

-- Two lists sorted by key, combined in one pass: a key in both goes to
-- `both`, a key in one only to `onlyLeft` or `onlyRight`, and each says what
-- value the result keeps there, if any.
def Map.Spec.merge [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x):
    List (k, v) → List (k, w) → List (k, x)
  | Nil, ys => Map.Spec.mapMaybe onlyRight ys
  | Cons x xs, Nil => Map.Spec.mapMaybe onlyLeft (Cons x xs)
  | Cons x xs, Cons y ys =>
    if Map.Spec.isLess x.fst y.fst then Map.Spec.consEntry x.fst (Map.Spec.merge both onlyLeft onlyRight xs (Cons y ys)) (onlyLeft x.fst x.snd)
    else if Map.Spec.isLess y.fst x.fst then Map.Spec.consEntry y.fst (Map.Spec.merge both onlyLeft onlyRight (Cons x xs) ys) (onlyRight y.fst y.snd)
    else Map.Spec.consEntry x.fst (Map.Spec.merge both onlyLeft onlyRight xs ys) (both x.fst x.snd y.snd)

-- What `Map.unionWith`, `Map.intersectWith` and `Map.difference` do to the
-- entries.
def Map.Spec.unionWith [auto ord: Ord k] (f: v → v → v) (xs: List (k, v)) (ys: List (k, v)): List (k, v) :=
  Map.Spec.merge (key x y => Some (f x y)) (key x => Some x) (key y => Some y) xs ys

def Map.Spec.intersectWith [auto ord: Ord k] (f: v → w → x) (xs: List (k, v)) (ys: List (k, w)): List (k, x) :=
  Map.Spec.merge (key a b => Some (f a b)) (key a => None) (key b => None) xs ys

def Map.Spec.difference [auto ord: Ord k] (xs: List (k, v)) (ys: List (k, w)): List (k, v) :=
  Map.Spec.merge (key a b => None) (key a => Some a) (key b => None) xs ys

-- One step of `merge`, at a smaller, equal or larger first key.

theorem Map.Spec.mergeLess [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x)
    (kx: k) (vx: v) (xs: List (k, v)) (ky: k) (vy: w) (ys: List (k, w)) (c: Ord.compare kx ky = Less):
    Map.Spec.merge both onlyLeft onlyRight (Cons (kx, vx) xs) (Cons (ky, vy) ys)
      = Map.Spec.consEntry kx (Map.Spec.merge both onlyLeft onlyRight xs (Cons (ky, vy) ys)) (onlyLeft kx vx) :=
  rewrite c in rfl

theorem Map.Spec.mergeEqual [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x)
    (kx: k) (vx: v) (xs: List (k, v)) (ky: k) (vy: w) (ys: List (k, w)) (c: Ord.compare kx ky = Equal):
    Map.Spec.merge both onlyLeft onlyRight (Cons (kx, vx) xs) (Cons (ky, vy) ys)
      = Map.Spec.consEntry kx (Map.Spec.merge both onlyLeft onlyRight xs ys) (both kx vx vy) :=
  rewrite c, Eq.trans (ord.flip kx ky) (Eq.cong Ordering.flip c) in rfl

theorem Map.Spec.mergeGreater [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x)
    (kx: k) (vx: v) (xs: List (k, v)) (ky: k) (vy: w) (ys: List (k, w)) (c: Ord.compare kx ky = Greater):
    Map.Spec.merge both onlyLeft onlyRight (Cons (kx, vx) xs) (Cons (ky, vy) ys)
      = Map.Spec.consEntry ky (Map.Spec.merge both onlyLeft onlyRight (Cons (kx, vx) xs) ys) (onlyRight ky vy) :=
  rewrite c, Map.Tree.lessOfGreater ord kx ky c in rfl

theorem Map.Spec.mergeNilRight [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x):
    (xs: List (k, v)) → Map.Spec.merge both onlyLeft onlyRight xs Nil = Map.Spec.mapMaybe onlyLeft xs
  | Nil => rfl
  | Cons (kx, vx) xs => rfl

-- A key below every key of `xs` is merged first.
theorem Map.Spec.mergeBelow [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x)
    (key: k) (value: w) (rest: List (k, w)):
    (xs: List (k, v)) → Map.Spec.Ascending ord (Some key) xs →
    Map.Spec.merge both onlyLeft onlyRight xs (Cons (key, value) rest)
      = Map.Spec.consEntry key (Map.Spec.merge both onlyLeft onlyRight xs rest) (onlyRight key value)
  | Nil, asc => rfl
  | Cons (kx, vx) xs, Both a axs =>
    Map.Spec.mergeGreater both onlyLeft onlyRight kx vx xs key value rest (Eq.trans (ord.flip key kx) (Eq.cong Ordering.flip a))

-- The results are sorted.

-- A list above `key` is above whatever `key` is above.
theorem Map.Spec.ascendingWeaken (ord: Ord k) (lo: Option k) (key: k) (h: Map.Tree.Above ord lo key):
    (xs: List (k, v)) → Map.Spec.Ascending ord (Some key) xs → Map.Spec.Ascending ord lo xs
  | Nil, asc => Trivial
  | Cons (a, x) rest, Both ka arest => Both (Map.Tree.aboveTrans ord lo key a h ka) arest

theorem Map.Spec.ascendingConsEntry (ord: Ord k) (lo: Option k) (key: k) (rest: List (k, x))
    (h: Map.Tree.Above ord lo key) (asc: Map.Spec.Ascending ord (Some key) rest):
    (o: Option x) → Map.Spec.Ascending ord lo (Map.Spec.consEntry key rest o)
  | Some value => Both h asc
  | None => Map.Spec.ascendingWeaken ord lo key h rest asc

theorem Map.Spec.mapMaybeAscending (ord: Ord k) (f: k → v → Option x): (lo: Option k) → (xs: List (k, v)) →
    Map.Spec.Ascending ord lo xs → Map.Spec.Ascending ord lo (Map.Spec.mapMaybe f xs)
  | lo, Nil, asc => Trivial
  | lo, Cons (kk, vv) rest, Both a arest =>
    Map.Spec.ascendingConsEntry ord lo kk (Map.Spec.mapMaybe f rest) a (Map.Spec.mapMaybeAscending ord f (Some kk) rest arest) (f kk vv)

theorem Map.Spec.mergeAscending [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x):
    (lo: Option k) → (xs: List (k, v)) → (ys: List (k, w)) →
    Map.Spec.Ascending ord lo xs → Map.Spec.Ascending ord lo ys →
    Map.Spec.Ascending ord lo (Map.Spec.merge both onlyLeft onlyRight xs ys)
  | lo, Nil, ys, ax, ay => Map.Spec.mapMaybeAscending ord onlyRight lo ys ay
  | lo, Cons (kx, vx) xs, ys, ax, ay =>
    Map.Spec.mergeAscendingCons both onlyLeft onlyRight kx vx xs
      (lo2 ys2 ax2 ay2 => Map.Spec.mergeAscending both onlyLeft onlyRight lo2 xs ys2 ax2 ay2) lo ys ax ay

-- `mergeAscending` for a nonempty first list, given it for the list's tail:
-- each proof recurses on one list.
theorem Map.Spec.mergeAscendingCons [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x)
    (kx: k) (vx: v) (xs: List (k, v))
    (tail: (lo: Option k) → (ys: List (k, w)) → Map.Spec.Ascending ord lo xs → Map.Spec.Ascending ord lo ys →
    Map.Spec.Ascending ord lo (Map.Spec.merge both onlyLeft onlyRight xs ys)):
    (lo: Option k) → (ys: List (k, w)) → Map.Spec.Ascending ord lo (Cons (kx, vx) xs) → Map.Spec.Ascending ord lo ys →
    Map.Spec.Ascending ord lo (Map.Spec.merge both onlyLeft onlyRight (Cons (kx, vx) xs) ys)
  | lo, Nil, ax, ay => Map.Spec.mapMaybeAscending ord onlyLeft lo (Cons (kx, vx) xs) ax
  | lo, Cons (ky, vy) ys, Both lx axs, Both ly ays =>
    match c: Ord.compare kx ky with
      | Less =>
        Map.Spec.ascendingConsEntry ord lo kx (Map.Spec.merge both onlyLeft onlyRight xs (Cons (ky, vy) ys)) lx
          (tail (Some kx) (Cons (ky, vy) ys) axs (Both c ays)) (onlyLeft kx vx)
      | Equal =>
        rewrite Eq.trans (ord.flip kx ky) (Eq.cong Ordering.flip c) in
        Map.Spec.ascendingConsEntry ord lo kx (Map.Spec.merge both onlyLeft onlyRight xs ys) lx
          (tail (Some kx) ys axs (rewrite ord.equal kx ky c in ays)) (both kx vx vy)
      | Greater =>
        rewrite Map.Tree.lessOfGreater ord kx ky c in
        Map.Spec.ascendingConsEntry ord lo ky (Map.Spec.merge both onlyLeft onlyRight (Cons (kx, vx) xs) ys) ly
          (Map.Spec.mergeAscendingCons both onlyLeft onlyRight kx vx xs tail (Some ky) ys (Both (Map.Tree.lessOfGreater ord kx ky c) axs) ays)
          (onlyRight ky vy)

theorem Map.Spec.filterAscending [auto ord: Ord k] (p: k → v → Bool): (lo: Option k) → (xs: List (k, v)) →
    Map.Spec.Ascending ord lo xs → Map.Spec.Ascending ord lo (List.filter xs (e => p e.fst e.snd))
  | lo, Nil, asc => Trivial
  | lo, Cons (kk, vv) rest, Both a arest =>
    match c: p kk vv with
      | True => Both a (Map.Spec.filterAscending p (Some kk) rest arest)
      | False => Map.Spec.ascendingWeaken ord lo kk a (List.filter rest (e => p e.fst e.snd)) (Map.Spec.filterAscending p (Some kk) rest arest)

-- What `lookupList` finds in the results.

theorem Map.Spec.lookupConsEntryEqual [auto ord: Ord k] (key: k) (kk: k) (rest: List (k, x))
    (e: Ord.compare key kk = Equal) (asc: Map.Spec.Ascending ord (Some kk) rest):
    (o: Option x) → Map.Tree.lookupList key (Map.Spec.consEntry kk rest o) = o
  | Some value => Map.Spec.lookupEqualHead key kk value rest e
  | None => Map.Spec.lookupBelow key kk rest asc (z => Ordering.equalNotGreater (Eq.trans (Eq.sym e) z))

theorem Map.Spec.lookupConsEntrySkip [auto ord: Ord k] (key: k) (kk: k) (rest: List (k, x))
    (ne: Not (Ord.compare key kk = Equal)):
    (o: Option x) → Map.Tree.lookupList key (Map.Spec.consEntry kk rest o) = Map.Tree.lookupList key rest
  | Some value => Map.Spec.lookupSkip key kk value rest ne
  | None => rfl

theorem Map.Spec.lookupMapMaybe [auto ord: Ord k] (f: k → v → Option x) (key: k): (lo: Option k) → (xs: List (k, v)) →
    Map.Spec.Ascending ord lo xs →
    Map.Tree.lookupList key (Map.Spec.mapMaybe f xs) = Option.flatMap (Map.Tree.lookupList key xs) (f key)
  | lo, Nil, asc => rfl
  | lo, Cons (kk, vv) rest, Both a arest =>
    match d: Ord.compare key kk with
      | Equal =>
        rewrite Map.Spec.lookupConsEntryEqual key kk (Map.Spec.mapMaybe f rest) d (Map.Spec.mapMaybeAscending ord f (Some kk) rest arest) (f kk vv),
          ord.equal key kk d in
        rfl
      | Less =>
        rewrite Map.Spec.lookupConsEntrySkip key kk (Map.Spec.mapMaybe f rest) (z => Ordering.lessNotEqual (Eq.trans (Eq.sym d) z)) (f kk vv) in
        Map.Spec.lookupMapMaybe f key (Some kk) rest arest
      | Greater =>
        rewrite Map.Spec.lookupConsEntrySkip key kk (Map.Spec.mapMaybe f rest) (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym d) z)) (f kk vv) in
        Map.Spec.lookupMapMaybe f key (Some kk) rest arest

-- What a merge has at `key`, from what each list has there.
def Map.Spec.mergeAt (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x) (key: k):
    Option v → Option w → Option x
  | Some a, Some b => both key a b
  | Some a, None => onlyLeft key a
  | None, Some b => onlyRight key b
  | None, None => None

theorem Map.Spec.mergeAtNoneLeft (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x) (key: k):
    (o: Option w) → Map.Spec.mergeAt both onlyLeft onlyRight key None o = Option.flatMap o (onlyRight key)
  | None => rfl
  | Some b => rfl

theorem Map.Spec.mergeAtNoneRight (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x) (key: k):
    (o: Option v) → Map.Spec.mergeAt both onlyLeft onlyRight key o None = Option.flatMap o (onlyLeft key)
  | None => rfl
  | Some a => rfl

theorem Map.Spec.lookupMerge [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x) (key: k):
    (lo: Option k) → (xs: List (k, v)) → (ys: List (k, w)) →
    Map.Spec.Ascending ord lo xs → Map.Spec.Ascending ord lo ys →
    Map.Tree.lookupList key (Map.Spec.merge both onlyLeft onlyRight xs ys)
      = Map.Spec.mergeAt both onlyLeft onlyRight key (Map.Tree.lookupList key xs) (Map.Tree.lookupList key ys)
  | lo, Nil, ys, ax, ay =>
    Eq.trans (Map.Spec.lookupMapMaybe onlyRight key lo ys ay)
      (Eq.sym (Map.Spec.mergeAtNoneLeft both onlyLeft onlyRight key (Map.Tree.lookupList key ys)))
  | lo, Cons (kx, vx) xs, ys, ax, ay =>
    Map.Spec.lookupMergeCons both onlyLeft onlyRight key kx vx xs
      (lo2 ys2 ax2 ay2 => Map.Spec.lookupMerge both onlyLeft onlyRight key lo2 xs ys2 ax2 ay2) lo ys ax ay

-- `lookupMerge` for a nonempty first list, given it for the list's tail.
theorem Map.Spec.lookupMergeCons [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x) (key: k)
    (kx: k) (vx: v) (xs: List (k, v))
    (tail: (lo: Option k) → (ys: List (k, w)) → Map.Spec.Ascending ord lo xs → Map.Spec.Ascending ord lo ys →
      Map.Tree.lookupList key (Map.Spec.merge both onlyLeft onlyRight xs ys)
        = Map.Spec.mergeAt both onlyLeft onlyRight key (Map.Tree.lookupList key xs) (Map.Tree.lookupList key ys)):
    (lo: Option k) → (ys: List (k, w)) → Map.Spec.Ascending ord lo (Cons (kx, vx) xs) → Map.Spec.Ascending ord lo ys →
    Map.Tree.lookupList key (Map.Spec.merge both onlyLeft onlyRight (Cons (kx, vx) xs) ys)
      = Map.Spec.mergeAt both onlyLeft onlyRight key (Map.Tree.lookupList key (Cons (kx, vx) xs)) (Map.Tree.lookupList key ys)
  | lo, Nil, ax, ay =>
    Eq.trans (Map.Spec.lookupMapMaybe onlyLeft key lo (Cons (kx, vx) xs) ax)
      (Eq.sym (Map.Spec.mergeAtNoneRight both onlyLeft onlyRight key (Map.Tree.lookupList key (Cons (kx, vx) xs))))
  | lo, Cons (ky, vy) ys, Both lx axs, Both ly ays =>
    match c: Ord.compare kx ky with
      | Less =>
        match d: Ord.compare key kx with
          | Equal =>
            rewrite Map.Spec.lookupConsEntryEqual key kx (Map.Spec.merge both onlyLeft onlyRight xs (Cons (ky, vy) ys)) d
                (Map.Spec.mergeAscending both onlyLeft onlyRight (Some kx) xs (Cons (ky, vy) ys) axs (Both c ays)) (onlyLeft kx vx),
              Map.Spec.lookupAbsentHead key ky vy ys (rewrite ord.equal key kx d in c) ays,
              ord.equal key kx d in
            rfl
          | Less =>
            rewrite Map.Spec.lookupConsEntrySkip key kx (Map.Spec.merge both onlyLeft onlyRight xs (Cons (ky, vy) ys))
              (z => Ordering.lessNotEqual (Eq.trans (Eq.sym d) z)) (onlyLeft kx vx) in
            tail (Some kx) (Cons (ky, vy) ys) axs (Both c ays)
          | Greater =>
            rewrite Map.Spec.lookupConsEntrySkip key kx (Map.Spec.merge both onlyLeft onlyRight xs (Cons (ky, vy) ys))
              (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym d) z)) (onlyLeft kx vx) in
            tail (Some kx) (Cons (ky, vy) ys) axs (Both c ays)
      | Equal =>
        rewrite Eq.trans (ord.flip kx ky) (Eq.cong Ordering.flip c) in
        match d: Ord.compare key kx with
          | Equal =>
            rewrite Map.Spec.lookupConsEntryEqual key kx (Map.Spec.merge both onlyLeft onlyRight xs ys) d
                (Map.Spec.mergeAscending both onlyLeft onlyRight (Some kx) xs ys axs (rewrite ord.equal kx ky c in ays)) (both kx vx vy),
              Map.Spec.lookupEqualHead key ky vy ys (rewrite Eq.sym (ord.equal kx ky c) in d),
              ord.equal key kx d in
            rfl
          | Less =>
            rewrite Map.Spec.lookupConsEntrySkip key kx (Map.Spec.merge both onlyLeft onlyRight xs ys)
                (z => Ordering.lessNotEqual (Eq.trans (Eq.sym d) z)) (both kx vx vy),
              Map.Spec.lookupSkip key ky vy ys (z => Ordering.lessNotEqual (Eq.trans (Eq.sym d) (rewrite ord.equal kx ky c in z))) in
            tail (Some kx) ys axs (rewrite ord.equal kx ky c in ays)
          | Greater =>
            rewrite Map.Spec.lookupConsEntrySkip key kx (Map.Spec.merge both onlyLeft onlyRight xs ys)
                (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym d) z)) (both kx vx vy),
              Map.Spec.lookupSkip key ky vy ys (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym d) (rewrite ord.equal kx ky c in z))) in
            tail (Some kx) ys axs (rewrite ord.equal kx ky c in ays)
      | Greater =>
        rewrite Map.Tree.lessOfGreater ord kx ky c in
        match d: Ord.compare key ky with
          | Equal =>
            rewrite Map.Spec.lookupConsEntryEqual key ky (Map.Spec.merge both onlyLeft onlyRight (Cons (kx, vx) xs) ys) d
                (Map.Spec.mergeAscending both onlyLeft onlyRight (Some ky) (Cons (kx, vx) xs) ys
                  (Both (Map.Tree.lessOfGreater ord kx ky c) axs) ays)
                (onlyRight ky vy),
              Map.Spec.lookupAbsentHead key kx vx xs (rewrite ord.equal key ky d in Map.Tree.lessOfGreater ord kx ky c) axs,
              ord.equal key ky d in
            rfl
          | Less =>
            rewrite Map.Spec.lookupConsEntrySkip key ky (Map.Spec.merge both onlyLeft onlyRight (Cons (kx, vx) xs) ys)
              (z => Ordering.lessNotEqual (Eq.trans (Eq.sym d) z)) (onlyRight ky vy) in
            Map.Spec.lookupMergeCons both onlyLeft onlyRight key kx vx xs tail (Some ky) ys
              (Both (Map.Tree.lessOfGreater ord kx ky c) axs) ays
          | Greater =>
            rewrite Map.Spec.lookupConsEntrySkip key ky (Map.Spec.merge both onlyLeft onlyRight (Cons (kx, vx) xs) ys)
              (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym d) z)) (onlyRight ky vy) in
            Map.Spec.lookupMergeCons both onlyLeft onlyRight key kx vx xs tail (Some ky) ys
              (Both (Map.Tree.lessOfGreater ord kx ky c) axs) ays

-- `unionWith` agrees with the fold of `insertWith` (`Map.Spec.foldInsertWith`),
-- so `Map.Raw.unionWith` may take either route.

-- Inserting a key below every key of `xs` and merging is merging it in.
theorem Map.Spec.unionWithInsert [auto ord: Ord k] (f: v → v → v) (kx: k) (vx: v) (xs: List (k, v))
    (axs: Map.Spec.Ascending ord (Some kx) xs):
    (ys: List (k, v)) →
    Map.Spec.merge (key x y => Some (f x y)) (key x => Some x) (key y => Some y) xs (Map.Spec.insertWith f kx vx ys)
      = Map.Spec.merge (key x y => Some (f x y)) (key x => Some x) (key y => Some y) (Cons (kx, vx) xs) ys
  | Nil =>
    Eq.trans (Map.Spec.mergeBelow (key x y => Some (f x y)) (key x => Some x) (key y => Some y) kx vx Nil xs axs)
      (Eq.cong (zs => Cons (kx, vx) zs) (Map.Spec.mergeNilRight (key x y => Some (f x y)) (key x => Some x) (key y => Some y) xs))
  | Cons (ky, vy) ys =>
    match c: Ord.compare kx ky with
      | Less =>
        Map.Spec.mergeBelow (key x y => Some (f x y)) (key x => Some x) (key y => Some y) kx vx (Cons (ky, vy) ys) xs axs
      | Equal =>
        rewrite Eq.trans (ord.flip kx ky) (Eq.cong Ordering.flip c),
          Map.Spec.mergeBelow (key x y => Some (f x y)) (key x => Some x) (key y => Some y) ky (f vx vy) ys xs
            (rewrite Eq.sym (ord.equal kx ky c) in axs),
          ord.equal kx ky c in
        rfl
      | Greater =>
        rewrite Map.Tree.lessOfGreater ord kx ky c,
          Map.Spec.mergeBelow (key x y => Some (f x y)) (key x => Some x) (key y => Some y) ky vy (Map.Spec.insertWith f kx vx ys) xs
            (Map.Spec.ascendingWeaken ord (Some ky) kx (Map.Tree.lessOfGreater ord kx ky c) xs axs),
          Map.Spec.unionWithInsert f kx vx xs axs ys in
        rfl

theorem Map.Spec.mapMaybeSome: (ys: List (k, v)) → Map.Spec.mapMaybe (key y => Some y) ys = ys
  | Nil => rfl
  | Cons (ky, vy) ys => Eq.cong (zs => Cons (ky, vy) zs) (Map.Spec.mapMaybeSome ys)

-- Inserting a sorted list's entries in turn, combining with `f`, is merging it in.
theorem Map.Spec.foldInsertWith [auto ord: Ord k] (f: v → v → v): (lo: Option k) → (xs: List (k, v)) → (ys: List (k, v)) →
    Map.Spec.Ascending ord lo xs →
    Map.Spec.foldLeft (l key value => Map.Spec.insertWith f key value l) ys xs = Map.Spec.unionWith f xs ys
  | lo, Nil, ys, asc => Eq.sym (Map.Spec.mapMaybeSome ys)
  | lo, Cons (kx, vx) xs, ys, Both a axs =>
    Eq.trans (Map.Spec.foldInsertWith f (Some kx) xs (Map.Spec.insertWith f kx vx ys) axs)
      (Map.Spec.unionWithInsert f kx vx xs axs ys)

-- What `lookupList` finds after each.

theorem Map.Spec.mergeAtUnionWith (f: v → v → v) (key: k): (a: Option v) → (b: Option v) →
    Map.Spec.mergeAt (key2 x y => Some (f x y)) (key2 x => Some x) (key2 y => Some y) key a b = Option.merge a b f
  | Some x, Some y => rfl
  | Some x, None => rfl
  | None, Some y => rfl
  | None, None => rfl

theorem Map.Spec.mergeAtIntersectWith (f: v → w → x) (key: k): (a: Option v) → (b: Option w) →
    Map.Spec.mergeAt (key2 x y => Some (f x y)) (key2 x => None) (key2 y => None) key a b
      = Option.flatMap a (value => Option.map b (f value))
  | Some x, Some y => rfl
  | Some x, None => rfl
  | None, Some y => rfl
  | None, None => rfl

theorem Map.Spec.mergeAtDifference (key: k): (a: Option v) → (b: Option w) →
    Map.Spec.mergeAt (key2 x y => None) (key2 x => Some x) (key2 y => None) key a b = Option.filter a (value => ¬(Option.isSome b))
  | Some x, Some y => rfl
  | Some x, None => rfl
  | None, Some y => rfl
  | None, None => rfl

-- Building a balanced tree from a sorted list, in one pass

-- `drop` facts for the entries a build leaves over.

theorem Map.Tree.dropNil: (n: Nat) → List.drop (Nil: List a) n = Nil
  | Zero => rfl
  | Succ n => rfl

theorem Map.Tree.dropAdd: (n: Nat) → (m: Nat) → (xs: List a) → List.drop xs (n + m) = List.drop (List.drop xs n) m
  | Zero, m, xs => rfl
  | Succ n, m, Nil => Eq.sym (Map.Tree.dropNil m)
  | Succ n, m, Cons x xs => Map.Tree.dropAdd n m xs

theorem Map.Tree.dropLength: (xs: List a) → List.drop xs (List.length xs) = Nil
  | Nil => rfl
  | Cons x xs => Map.Tree.dropLength xs

theorem Map.Tree.halfLe (m: Nat): m / 2 ≤ m := Nat.leTrans (m / 2) (m / 2 * 2) m (Nat.leMulPos (m / 2) 2 rfl) (Nat.divFuelLe m m 2)

-- The first key, if any.
def Map.Spec.headKey: List (k, v) → Option k
  | Nil => None
  | Cons (kk, vv) rest => Some kk

-- A node from a left tree and the entries after it: the next entry is its
-- key, and `buildRight` builds its right tree from the ones after that. If
-- there's no next entry, the left tree is all there is.
def Map.Tree.joinBuilt (buildRight: List (k, v) → (Map.Tree k v, List (k, v))) (left: (Map.Tree k v, List (k, v))):
    (Map.Tree k v, List (k, v)) :=
  match left.snd with
    | Nil => left
    | Cons (key, value) rest =>
      let right := buildRight rest
      (Map.Tree.bin left.fst key value right.fst, right.snd)

-- A tree of the first `n` entries of `entries` (all of them if there are
-- fewer), half on each side of each node, and the entries after them: O(n).
-- `fuel` keeps the recursion structural; it is never less than `n`, so it
-- never runs out.
def Map.Tree.buildFuel: Nat → Nat → List (k, v) → (Map.Tree k v, List (k, v))
  | Zero, n, entries => (Tip, entries)
  | Succ fuel, Zero, entries => (Tip, entries)
  | Succ fuel, Succ m, entries =>
    Map.Tree.joinBuilt (rest => Map.Tree.buildFuel fuel (m - m / 2) rest) (Map.Tree.buildFuel fuel (m / 2) entries)

-- The tree's entries, followed by those left over, are the entries.
theorem Map.Tree.joinBuiltOnto (buildRight: List (k, v) → (Map.Tree k v, List (k, v)))
    (h: (rest: List (k, v)) → Map.Tree.toListOnto (buildRight rest).fst (buildRight rest).snd = rest):
    (left: (Map.Tree k v, List (k, v))) → (xs: List (k, v)) → Map.Tree.toListOnto left.fst left.snd = xs →
    Map.Tree.toListOnto (Map.Tree.joinBuilt buildRight left).fst (Map.Tree.joinBuilt buildRight left).snd = xs
  | (l, Nil), xs, hl => hl
  | (l, Cons (key, value) rest), xs, hl => rewrite h rest in hl

theorem Map.Tree.buildOnto: (fuel: Nat) → (n: Nat) → (xs: List (k, v)) →
    Map.Tree.toListOnto (Map.Tree.buildFuel fuel n xs).fst (Map.Tree.buildFuel fuel n xs).snd = xs
  | Zero, n, xs => rfl
  | Succ fuel, Zero, xs => rfl
  | Succ fuel, Succ m, xs =>
    Map.Tree.joinBuiltOnto (rest => Map.Tree.buildFuel fuel (m - m / 2) rest) (rest => Map.Tree.buildOnto fuel (m - m / 2) rest)
      (Map.Tree.buildFuel fuel (m / 2) xs) xs (Map.Tree.buildOnto fuel (m / 2) xs)

theorem Map.Tree.joinBuiltSized (buildRight: List (k, v) → (Map.Tree k v, List (k, v)))
    (h: (rest: List (k, v)) → Map.Tree.Sized (buildRight rest).fst):
    (left: (Map.Tree k v, List (k, v))) → Map.Tree.Sized left.fst → Map.Tree.Sized (Map.Tree.joinBuilt buildRight left).fst
  | (l, Nil), sl => sl
  | (l, Cons (key, value) rest), sl => Map.Tree.binSized l key value (buildRight rest).fst sl (h rest)

theorem Map.Tree.buildSized: (fuel: Nat) → (n: Nat) → (xs: List (k, v)) → Map.Tree.Sized (Map.Tree.buildFuel fuel n xs).fst
  | Zero, n, xs => Trivial
  | Succ fuel, Zero, xs => Trivial
  | Succ fuel, Succ m, xs =>
    Map.Tree.joinBuiltSized (rest => Map.Tree.buildFuel fuel (m - m / 2) rest) (rest => Map.Tree.buildSized fuel (m - m / 2) rest)
      (Map.Tree.buildFuel fuel (m / 2) xs) (Map.Tree.buildSized fuel (m / 2) xs)

-- Keys in order: the tree's keys are above `lo` and below the first key
-- left over, and the entries left over stay above `lo`.
def Map.Tree.BuiltWithin (ord: Ord k) (lo: Option k) (built: (Map.Tree k v, List (k, v))): Prop :=
  And (Map.Tree.Within ord lo (Map.Spec.headKey built.snd) built.fst) (Map.Spec.Ascending ord lo built.snd)

theorem Map.Spec.belowHeadKey (ord: Ord k) (key: k): (xs: List (k, v)) →
    Map.Spec.Ascending ord (Some key) xs → Map.Tree.Below ord key (Map.Spec.headKey xs)
  | Nil, asc => Trivial
  | Cons (a, x) rest, Both ka arest => ka

theorem Map.Tree.joinBuiltWithin (ord: Ord k) (buildRight: List (k, v) → (Map.Tree k v, List (k, v)))
    (h: (lo: Option k) → (rest: List (k, v)) → Map.Spec.Ascending ord lo rest → Map.Tree.BuiltWithin ord lo (buildRight rest)):
    (left: (Map.Tree k v, List (k, v))) → (lo: Option k) → Map.Tree.BuiltWithin ord lo left →
    Map.Tree.BuiltWithin ord lo (Map.Tree.joinBuilt buildRight left)
  | (l, Nil), lo, hl => hl
  | (l, Cons (key, value) rest), lo, Both wl (Both akey arest) =>
    match h (Some key) rest arest with
      | Both wr asc =>
        Both
          (Both (Both akey (Map.Spec.belowHeadKey ord key (buildRight rest).snd asc)) (Both wl wr))
          (Map.Spec.ascendingWeaken ord lo key akey (buildRight rest).snd asc)

theorem Map.Tree.buildWithin (ord: Ord k): (fuel: Nat) → (n: Nat) → (lo: Option k) → (xs: List (k, v)) →
    Map.Spec.Ascending ord lo xs → Map.Tree.BuiltWithin ord lo (Map.Tree.buildFuel fuel n xs)
  | Zero, n, lo, xs, asc => Both Trivial asc
  | Succ fuel, Zero, lo, xs, asc => Both Trivial asc
  | Succ fuel, Succ m, lo, xs, asc =>
    Map.Tree.joinBuiltWithin ord (rest => Map.Tree.buildFuel fuel (m - m / 2) rest)
      (lo2 rest asc2 => Map.Tree.buildWithin ord fuel (m - m / 2) lo2 rest asc2)
      (Map.Tree.buildFuel fuel (m / 2) xs) lo (Map.Tree.buildWithin ord fuel (m / 2) lo xs asc)

-- With enough fuel, what's left over is what `drop` leaves.
theorem Map.Tree.joinBuiltRest (buildRight: List (k, v) → (Map.Tree k v, List (k, v))) (r: Nat)
    (h: (rest: List (k, v)) → (buildRight rest).snd = List.drop rest r):
    (left: (Map.Tree k v, List (k, v))) → (a: Nat) → (xs: List (k, v)) → left.snd = List.drop xs a →
    (Map.Tree.joinBuilt buildRight left).snd = List.drop xs (a + Succ r)
  | (l, Nil), a, xs, hl => rewrite Map.Tree.dropAdd a (Succ r) xs, Eq.sym hl in rfl
  | (l, Cons (key, value) rest), a, xs, hl => rewrite Map.Tree.dropAdd a (Succ r) xs, Eq.sym hl in h rest

theorem Map.Tree.buildRest: (fuel: Nat) → (n: Nat) → (xs: List (k, v)) → n ≤ fuel →
    (Map.Tree.buildFuel fuel n xs).snd = List.drop xs n
  | Zero, Zero, xs, h => rfl
  | Zero, Succ m, xs, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ fuel, Zero, xs, h => rfl
  | Succ fuel, Succ m, xs, h =>
    Eq.trans
      (Map.Tree.joinBuiltRest (rest => Map.Tree.buildFuel fuel (m - m / 2) rest) (m - m / 2)
        (rest => Map.Tree.buildRest fuel (m - m / 2) rest (Nat.leTrans (m - m / 2) m fuel (Nat.subLe m (m / 2)) h))
        (Map.Tree.buildFuel fuel (m / 2) xs) (m / 2) xs
        (Map.Tree.buildRest fuel (m / 2) xs (Nat.leTrans (m / 2) m fuel (Map.Tree.halfLe m) h)))
      (Eq.cong (n => List.drop xs n)
        (Eq.trans (Nat.addSucc (m / 2) (m - m / 2)) (Eq.cong Succ (Nat.addSubCancel (m / 2) m (Map.Tree.halfLe m)))))

theorem Map.Tree.withinNoneHigh (ord: Ord k) (lo: Option k) (t: Map.Tree k v): (hi: Option k) → Map.Tree.Within ord lo hi t → Map.Tree.Within ord lo None t
  | None, w => w
  | Some a, w => Map.Tree.withinHigh ord lo a None t Trivial w

-- The number of entries, counted onto `count` in a loop: `List.length`
-- recurses once per entry, which overflows the stack in JS for long lists.
def Map.Spec.countOnto: Nat → List (k, v) → Nat
  | count, Nil => count
  | count, Cons entry rest => Map.Spec.countOnto (Succ count) rest

def Map.Spec.countEntries (xs: List (k, v)): Nat := Map.Spec.countOnto 0 xs

theorem Map.Spec.countOntoLength: (count: Nat) → (xs: List (k, v)) → Map.Spec.countOnto count xs = List.length xs + count
  | count, Nil => rfl
  | count, Cons entry rest => Eq.trans (Map.Spec.countOntoLength (Succ count) rest) (Nat.addSucc (List.length rest) count)

theorem Map.Spec.countEntriesLength (xs: List (k, v)): Map.Spec.countEntries xs = List.length xs :=
  Eq.trans (Map.Spec.countOntoLength 0 xs) (Nat.addZero (List.length xs))

theorem Map.Spec.dropCountEntries (xs: List (k, v)): List.drop xs (Map.Spec.countEntries xs) = Nil :=
  rewrite Map.Spec.countEntriesLength xs in Map.Tree.dropLength xs

-- The raw map of a sorted list's entries, O(n).
def Map.Raw.fromSorted [auto ord: Ord k] (xs: List (k, v)) (sorted: Map.Spec.Sorted ord xs): Map.Raw k v := {
  tree = (Map.Tree.buildFuel (Map.Spec.countEntries xs) (Map.Spec.countEntries xs) xs).fst,
  ordered =
    Map.Tree.withinNoneHigh ord None (Map.Tree.buildFuel (Map.Spec.countEntries xs) (Map.Spec.countEntries xs) xs).fst
      (Map.Spec.headKey (Map.Tree.buildFuel (Map.Spec.countEntries xs) (Map.Spec.countEntries xs) xs).snd)
      (Map.Tree.buildWithin ord (Map.Spec.countEntries xs) (Map.Spec.countEntries xs) None xs sorted).left,
  sized = Map.Tree.buildSized (Map.Spec.countEntries xs) (Map.Spec.countEntries xs) xs
}

theorem Map.Raw.toListFromSorted [auto ord: Ord k] (xs: List (k, v)) (sorted: Map.Spec.Sorted ord xs):
    Map.Raw.toList (Map.Raw.fromSorted xs sorted) = xs :=
  Eq.trans
    (Eq.cong (rest => Map.Tree.toListOnto (Map.Tree.buildFuel (Map.Spec.countEntries xs) (Map.Spec.countEntries xs) xs).fst rest)
      (Eq.sym (Eq.trans (Map.Tree.buildRest (Map.Spec.countEntries xs) (Map.Spec.countEntries xs) xs (Nat.leRefl (Map.Spec.countEntries xs))) (Map.Spec.dropCountEntries xs))))
    (Map.Tree.buildOnto (Map.Spec.countEntries xs) (Map.Spec.countEntries xs) xs)

-- Whether the keys are ascending, each above `lo`: one pass, O(n).
def Map.Spec.isAscending [auto ord: Ord k]: Option k → List (k, v) → Bool
  | lo, Nil => True
  | None, Cons (kk, vv) rest => Map.Spec.isAscending (Some kk) rest
  | Some lo, Cons (kk, vv) rest => if Map.Spec.isLess lo kk then Map.Spec.isAscending (Some kk) rest else False

theorem Map.Spec.ascendingOfCheck [auto ord: Ord k]: (lo: Option k) → (xs: List (k, v)) → Map.Spec.isAscending lo xs = True →
    Map.Spec.Ascending ord lo xs
  | lo, Nil, h => Trivial
  | None, Cons (kk, vv) rest, h => Both Trivial (Map.Spec.ascendingOfCheck (Some kk) rest h)
  | Some lo, Cons (kk, vv) rest, h =>
    match c: Ord.compare lo kk with
      | Less => Both rfl (Map.Spec.ascendingOfCheck (Some kk) rest h)
      | Equal => Void.exfalso (Bool.falseNotTrue h)
      | Greater => Void.exfalso (Bool.falseNotTrue h)

-- On ascending keys the last entry for a key is the only one.
theorem Map.Spec.lookupLastAscending [auto ord: Ord k] (key: k): (lo: Option k) → (xs: List (k, v)) → Map.Spec.Ascending ord lo xs →
    Map.lookupLast key xs = Map.Tree.lookupList key xs
  | lo, Nil, asc => rfl
  | lo, Cons (kk, vv) rest, Both a arest =>
    rewrite Map.Spec.lookupLastAscending key (Some kk) rest arest in
    match d: Ord.compare key kk with
      | Equal => rewrite Map.Spec.lookupBelow key kk rest arest (z => Ordering.equalNotGreater (Eq.trans (Eq.sym d) z)), d in rfl
      | Less => rewrite Map.Spec.lookupBelow key kk rest arest (z => Ordering.lessNotGreater (Eq.trans (Eq.sym d) z)), d in rfl
      | Greater =>
        match e: Map.Tree.lookupList key rest with
          | Some x => rfl
          | None => rewrite d in rfl

-- `fromList`, but O(n) when the keys come in ascending order: then the tree
-- is built from the list directly.
def Map.Raw.fromListFast [auto ord: Ord k] (xs: List (k, v)): Map.Raw k v :=
  Map.Raw.fromListChecked xs (Map.Spec.isAscending None xs) rfl

-- `fromListFast`, given whether the keys are ascending.
def Map.Raw.fromListChecked [auto ord: Ord k] (xs: List (k, v)): (ascending: Bool) → Map.Spec.isAscending None xs = ascending → Map.Raw k v
  | True, h => Map.Raw.fromSorted xs (Map.Spec.ascendingOfCheck None xs h)
  | False, h => Map.Raw.fromList xs

theorem Map.Raw.toListFromListFast [auto ord: Ord k] (xs: List (k, v)):
    Map.Raw.toList (Map.Raw.fromListFast xs) = Map.Spec.fromList xs :=
  Map.Raw.toListFromListChecked xs (Map.Spec.isAscending None xs) rfl

theorem Map.Raw.toListFromListChecked [auto ord: Ord k] (xs: List (k, v)): (ascending: Bool) → (c: Map.Spec.isAscending None xs = ascending) →
    Map.Raw.toList (Map.Raw.fromListChecked xs ascending c) = Map.Spec.fromList xs
  | True, c =>
    Eq.trans (Map.Raw.toListFromSorted xs (Map.Spec.ascendingOfCheck None xs c))
      (Map.Spec.extLookup None xs (Map.Spec.fromList xs) (Map.Spec.ascendingOfCheck None xs c)
        (rewrite <- Map.Raw.toListFromList xs in Map.Raw.toListSorted (Map.Raw.fromList xs))
        (key =>
          Eq.trans (Eq.sym (Map.Spec.lookupLastAscending key None xs (Map.Spec.ascendingOfCheck None xs c)))
            (Eq.trans (Eq.sym (Map.Raw.getFromList key xs))
              (Eq.trans (Map.Raw.getToList key (Map.Raw.fromList xs)) (Eq.cong (Map.Tree.lookupList key) (Map.Raw.toListFromList xs))))))
  | False, c => Map.Raw.toListFromList xs

theorem Map.Raw.getFromListFast [auto ord: Ord k] (key: k) (xs: List (k, v)):
    Map.Raw.get key (Map.Raw.fromListFast xs) = Map.lookupLast key xs :=
  Eq.trans (Map.Raw.getToList key (Map.Raw.fromListFast xs))
    (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.Raw.toListFromListFast xs))
      (Eq.trans (Eq.sym (Eq.cong (Map.Tree.lookupList key) (Map.Raw.toListFromList xs)))
        (Eq.trans (Eq.sym (Map.Raw.getToList key (Map.Raw.fromList xs))) (Map.Raw.getFromList key xs))))

-- The raw operations

-- Two raw maps merged entry by entry (see `Map.Spec.merge`).
@[noReceiver]
def Map.Raw.merge [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x)
    (a: Map.Raw k v) (b: Map.Raw k w): Map.Raw k x :=
  Map.Raw.fromSorted (Map.Spec.merge both onlyLeft onlyRight (Map.Raw.toList a) (Map.Raw.toList b))
    (Map.Spec.mergeAscending both onlyLeft onlyRight None (Map.Raw.toList a) (Map.Raw.toList b) (Map.Raw.toListSorted a) (Map.Raw.toListSorted b))

theorem Map.Raw.toListMerge [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x)
    (a: Map.Raw k v) (b: Map.Raw k w):
    Map.Raw.toList (Map.Raw.merge both onlyLeft onlyRight a b) = Map.Spec.merge both onlyLeft onlyRight (Map.Raw.toList a) (Map.Raw.toList b) :=
  Map.Raw.toListFromSorted (Map.Spec.merge both onlyLeft onlyRight (Map.Raw.toList a) (Map.Raw.toList b))
    (Map.Spec.mergeAscending both onlyLeft onlyRight None (Map.Raw.toList a) (Map.Raw.toList b) (Map.Raw.toListSorted a) (Map.Raw.toListSorted b))

-- The entries `f` keeps, with the values it gives, O(n).
@[noReceiver]
def Map.Raw.mapMaybe [auto ord: Ord k] (f: k → v → Option w) (m: Map.Raw k v): Map.Raw k w :=
  Map.Raw.fromSorted (Map.Spec.mapMaybe f (Map.Raw.toList m)) (Map.Spec.mapMaybeAscending ord f None (Map.Raw.toList m) (Map.Raw.toListSorted m))

theorem Map.Raw.toListMapMaybe [auto ord: Ord k] (f: k → v → Option w) (m: Map.Raw k v):
    Map.Raw.toList (Map.Raw.mapMaybe f m) = Map.Spec.mapMaybe f (Map.Raw.toList m) :=
  Map.Raw.toListFromSorted (Map.Spec.mapMaybe f (Map.Raw.toList m)) (Map.Spec.mapMaybeAscending ord f None (Map.Raw.toList m) (Map.Raw.toListSorted m))

-- The entries for which `p` holds, O(n).
@[noReceiver]
def Map.Raw.filter [auto ord: Ord k] (p: k → v → Bool) (m: Map.Raw k v): Map.Raw k v :=
  Map.Raw.fromSorted (List.filter (Map.Raw.toList m) (e => p e.fst e.snd)) (Map.Spec.filterAscending p None (Map.Raw.toList m) (Map.Raw.toListSorted m))

-- Whether `a` is small enough beside `b` to work key by key: O(n log m)
-- against the merge's O(n + m).
def Map.Raw.isSmall (a: Map.Raw k v [ord := o]) (b: Map.Raw k w [ord := o]): Bool := Nat.leq (Map.Raw.size a * 8) (Map.Raw.size b)

-- Both maps' entries; where both have a key, `f` of the first map's value
-- and the second's.
@[noReceiver]
def Map.Raw.unionWith [auto ord: Ord k] (f: v → v → v) (a: Map.Raw k v) (b: Map.Raw k v): Map.Raw k v :=
  if Map.Raw.isSmall a b then Map.Raw.foldLeft (acc key value => Map.Raw.insertWith f key value acc) b a
  else if Map.Raw.isSmall b a then Map.Raw.foldLeft (acc key value => Map.Raw.insertWith (new old => f old new) key value acc) a b
  else Map.Raw.merge (key x y => Some (f x y)) (key x => Some x) (key y => Some y) a b

-- Both maps' entries; where both have a key, the first map's value.
def Map.Raw.union [auto ord: Ord k] (a: Map.Raw k v) (b: Map.Raw k v): Map.Raw k v := Map.Raw.unionWith (new old => new) a b

-- The keys of both maps, with `f` of their values.
@[noReceiver]
def Map.Raw.intersectWith [auto ord: Ord k] (f: v → w → x) (a: Map.Raw k v) (b: Map.Raw k w): Map.Raw k x :=
  if Map.Raw.isSmall a b then Map.Raw.mapMaybe (key value => Option.map (Map.Raw.get key b) (f value)) a
  else Map.Raw.merge (key x y => Some (f x y)) (key x => None) (key y => None) a b

-- The entries of `a` whose keys aren't in `b`.
def Map.Raw.difference [auto ord: Ord k] (a: Map.Raw k v) (b: Map.Raw k w): Map.Raw k v :=
  if Map.Raw.isSmall a b then Map.Raw.mapMaybe (key value => if Map.Raw.contains key b then None else Some value) a
  else if Map.Raw.isSmall b a then Map.Raw.foldLeft (acc key value => Map.Raw.remove key acc) a b
  else Map.Raw.merge (key x y => None) (key x => Some x) (key y => None) a b

-- What they do to the entries.

theorem Map.Raw.toListFilterList [auto ord: Ord k] (m: Map.Raw k v) (p: k → v → Bool):
    Map.Raw.toList (Map.Raw.filter p m) = List.filter (Map.Raw.toList m) (e => p e.fst e.snd) :=
  Map.Raw.toListFromSorted (List.filter (Map.Raw.toList m) (e => p e.fst e.snd)) (Map.Spec.filterAscending p None (Map.Raw.toList m) (Map.Raw.toListSorted m))

theorem Map.Raw.toListFilter [auto ord: Ord k] (p: k → v → Bool) (m: Map.Raw k v):
    Map.Raw.toList (Map.Raw.filter p m) = Map.Spec.filter p (Map.Raw.toList m) :=
  Eq.trans (Map.Raw.toListFilterList m p) (Eq.sym (Map.Spec.filterOnto p Nil (Map.Raw.toList m) (Map.Raw.toListSorted m)))

theorem Map.Raw.toListUnionWith [auto ord: Ord k] (f: v → v → v) (a: Map.Raw k v) (b: Map.Raw k v):
    Map.Raw.toList (Map.Raw.unionWith f a b) = Map.Spec.unionWith f (Map.Raw.toList a) (Map.Raw.toList b) :=
  match c: Map.Raw.isSmall a b with
    | True =>
      rewrite Map.Raw.foldLeftToList (acc key value => Map.Raw.insertWith f key value acc) b a in
      Eq.trans
        (Map.Raw.toListFold (acc key value => Map.Raw.insertWith f key value acc)
          ((l: List (k, v)) (key: k) (value: v) => Map.Spec.insertWith f key value l)
          (m key value => Map.Raw.toListInsertWith f key value m) b (Map.Raw.toList a))
        (Map.Spec.foldInsertWith f None (Map.Raw.toList a) (Map.Raw.toList b) (Map.Raw.toListSorted a))
    | False =>
      match d: Map.Raw.isSmall b a with
        | True =>
          rewrite Map.Raw.foldLeftToList (acc key value => Map.Raw.insertWith (new old => f old new) key value acc) a b in
          Eq.trans
            (Eq.trans
              (Map.Raw.toListFold (acc key value => Map.Raw.insertWith (new old => f old new) key value acc)
                ((l: List (k, v)) (key: k) (value: v) => Map.Spec.insertWith (new old => f old new) key value l)
                (m key value => Map.Raw.toListInsertWith (new old => f old new) key value m) a (Map.Raw.toList b))
              (Map.Spec.foldInsertWith (new old => f old new) None (Map.Raw.toList b) (Map.Raw.toList a) (Map.Raw.toListSorted b)))
            (Map.Spec.unionWithFlip f (Map.Raw.toList a) (Map.Raw.toList b) (Map.Raw.toListSorted a) (Map.Raw.toListSorted b))
        | False => Map.Raw.toListMerge (key x y => Some (f x y)) (key x => Some x) (key y => Some y) a b

theorem Map.Raw.toListUnion [auto ord: Ord k] (a: Map.Raw k v) (b: Map.Raw k v):
    Map.Raw.toList (Map.Raw.union a b) = Map.Spec.union (Map.Raw.toList a) (Map.Raw.toList b) :=
  Eq.trans (Map.Raw.toListUnionWith (new old => new) a b)
    (Eq.sym (Map.Spec.foldInsertWith (new old => new) None (Map.Raw.toList a) (Map.Raw.toList b) (Map.Raw.toListSorted a)))

-- Sorted lists in which `lookupList` finds what the merge finds are the merge.
theorem Map.Spec.mergeExt [auto ord: Ord k] (both: k → v → w → Option x) (onlyLeft: k → v → Option x) (onlyRight: k → w → Option x)
    (xs: List (k, v)) (ys: List (k, w)) (zs: List (k, x))
    (ax: Map.Spec.Sorted ord xs) (ay: Map.Spec.Sorted ord ys) (az: Map.Spec.Sorted ord zs)
    (same: (key: k) → Map.Tree.lookupList key zs = Map.Spec.mergeAt both onlyLeft onlyRight key (Map.Tree.lookupList key xs) (Map.Tree.lookupList key ys)):
    zs = Map.Spec.merge both onlyLeft onlyRight xs ys :=
  Map.Spec.extLookup None zs (Map.Spec.merge both onlyLeft onlyRight xs ys) az (Map.Spec.mergeAscending both onlyLeft onlyRight None xs ys ax ay)
    (key => Eq.trans (same key) (Eq.sym (Map.Spec.lookupMerge both onlyLeft onlyRight key None xs ys ax ay)))

theorem Option.mergeFlip (f: v → v → v): (a: Option v) → (b: Option v) → Option.merge b a (new old => f old new) = Option.merge a b f
  | Some x, Some y => rfl
  | Some x, None => rfl
  | None, Some y => rfl
  | None, None => rfl

-- Merging sorted lists the other way round, with `f`'s arguments swapped,
-- gives the same entries.
theorem Map.Spec.unionWithFlip [auto ord: Ord k] (f: v → v → v) (xs: List (k, v)) (ys: List (k, v))
    (ax: Map.Spec.Sorted ord xs) (ay: Map.Spec.Sorted ord ys):
    Map.Spec.unionWith (new old => f old new) ys xs = Map.Spec.unionWith f xs ys :=
  Map.Spec.mergeExt (key x y => Some (f x y)) (key x => Some x) (key y => Some y) xs ys
    (Map.Spec.unionWith (new old => f old new) ys xs) ax ay
    (Map.Spec.mergeAscending (key x y => Some (f y x)) (key x => Some x) (key y => Some y) None ys xs ay ax)
    (key =>
      Eq.trans
        (Map.Spec.lookupMerge (key2 x y => Some (f y x)) (key2 x => Some x) (key2 y => Some y) key None ys xs ay ax)
        (Eq.trans (Map.Spec.mergeAtUnionWith (new old => f old new) key (Map.Tree.lookupList key ys) (Map.Tree.lookupList key xs))
          (Eq.trans (Option.mergeFlip f (Map.Tree.lookupList key xs) (Map.Tree.lookupList key ys))
            (Eq.sym (Map.Spec.mergeAtUnionWith f key (Map.Tree.lookupList key xs) (Map.Tree.lookupList key ys))))))

theorem Map.Raw.containsIsSome [auto ord: Ord k] (key: k) (m: Map.Raw k v): Map.Raw.contains key m = Option.isSome (Map.Raw.get key m) :=
  match c: Map.Raw.get key m with
    | Some value => rfl
    | None => rfl

theorem Map.Raw.toListIntersectWith [auto ord: Ord k] (f: v → w → x) (a: Map.Raw k v) (b: Map.Raw k w):
    Map.Raw.toList (Map.Raw.intersectWith f a b) = Map.Spec.intersectWith f (Map.Raw.toList a) (Map.Raw.toList b) :=
  match c: Map.Raw.isSmall a b with
    | True =>
      Map.Spec.mergeExt (key x y => Some (f x y)) (key x => None) (key y => None) (Map.Raw.toList a) (Map.Raw.toList b)
        (Map.Raw.toList (Map.Raw.mapMaybe (key value => Option.map (Map.Raw.get key b) (f value)) a))
        (Map.Raw.toListSorted a) (Map.Raw.toListSorted b)
        (Map.Raw.toListSorted (Map.Raw.mapMaybe (key value => Option.map (Map.Raw.get key b) (f value)) a))
        (key =>
          Eq.trans
            (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.Raw.toListMapMaybe (key2 value => Option.map (Map.Raw.get key2 b) (f value)) a))
              (Map.Spec.lookupMapMaybe (key2 value => Option.map (Map.Raw.get key2 b) (f value)) key None (Map.Raw.toList a) (Map.Raw.toListSorted a)))
            (Eq.trans
              (Eq.cong (o => Option.flatMap (Map.Tree.lookupList key (Map.Raw.toList a)) (value => Option.map o (f value))) (Map.Raw.getToList key b))
              (Eq.sym (Map.Spec.mergeAtIntersectWith f key (Map.Tree.lookupList key (Map.Raw.toList a)) (Map.Tree.lookupList key (Map.Raw.toList b))))))
    | False => Map.Raw.toListMerge (key x y => Some (f x y)) (key x => None) (key y => None) a b

-- `difference`'s key-by-key step finds what the merge finds.
theorem Map.Spec.mergeAtDifferenceStep (key: k) (present: Bool): (a: Option v) → (b: Option w) → present = Option.isSome b →
    Option.flatMap a (value => if present then None else Some value) = Map.Spec.mergeAt (key2 x y => None) (key2 x => Some x) (key2 y => None) key a b
  | None, None, h => rfl
  | None, Some y, h => rfl
  | Some x, None, h => rewrite h in rfl
  | Some x, Some y, h => rewrite h in rfl

theorem Map.Raw.toListDifference [auto ord: Ord k] (a: Map.Raw k v) (b: Map.Raw k w):
    Map.Raw.toList (Map.Raw.difference a b) = Map.Spec.difference (Map.Raw.toList a) (Map.Raw.toList b) :=
  match c: Map.Raw.isSmall a b with
    | True =>
      Map.Spec.mergeExt (key x y => None) (key x => Some x) (key y => None) (Map.Raw.toList a) (Map.Raw.toList b)
        (Map.Raw.toList (Map.Raw.mapMaybe (key value => if Map.Raw.contains key b then None else Some value) a))
        (Map.Raw.toListSorted a) (Map.Raw.toListSorted b)
        (Map.Raw.toListSorted (Map.Raw.mapMaybe (key value => if Map.Raw.contains key b then None else Some value) a))
        (key =>
          Eq.trans
            (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.Raw.toListMapMaybe (key2 value => if Map.Raw.contains key2 b then None else Some value) a))
              (Map.Spec.lookupMapMaybe (key2 value => if Map.Raw.contains key2 b then None else Some value) key None
                (Map.Raw.toList a) (Map.Raw.toListSorted a)))
            (Map.Spec.mergeAtDifferenceStep key (Map.Raw.contains key b) (Map.Tree.lookupList key (Map.Raw.toList a))
              (Map.Tree.lookupList key (Map.Raw.toList b))
              (Eq.trans (Map.Raw.containsIsSome key b) (Eq.cong Option.isSome (Map.Raw.getToList key b)))))
    | False =>
      match d: Map.Raw.isSmall b a with
        | True =>
          rewrite Map.Raw.foldLeftToList (acc key value => Map.Raw.remove key acc) a b in
          Map.Spec.mergeExt (key x y => None) (key x => Some x) (key y => None) (Map.Raw.toList a) (Map.Raw.toList b)
            (Map.Raw.toList (Map.Spec.foldLeft (acc key value => Map.Raw.remove key acc) a (Map.Raw.toList b)))
            (Map.Raw.toListSorted a) (Map.Raw.toListSorted b)
            (Map.Raw.toListSorted (Map.Spec.foldLeft (acc key value => Map.Raw.remove key acc) a (Map.Raw.toList b)))
            (key =>
              Eq.trans (Eq.sym (Map.Raw.getToList key (Map.Spec.foldLeft (acc key2 value => Map.Raw.remove key2 acc) a (Map.Raw.toList b))))
                (Eq.trans (Map.Raw.getFoldRemove key a (Map.Raw.toList b))
                  (rewrite Map.Raw.getToList key a in
                    Eq.sym (Map.Spec.mergeAtDifference key (Map.Tree.lookupList key (Map.Raw.toList a)) (Map.Tree.lookupList key (Map.Raw.toList b))))))
        | False => Map.Raw.toListMerge (key x y => None) (key x => Some x) (key y => None) a b

-- Removing each key of a list: what is left is what the list doesn't have.
theorem Map.Raw.getFoldRemove [auto ord: Ord k] (key: k): (m: Map.Raw k v) → (ys: List (k, w)) →
    Map.Raw.get key (Map.Spec.foldLeft (acc key2 value => Map.Raw.remove key2 acc) m ys)
      = Option.filter (Map.Raw.get key m) (value => ¬(Option.isSome (Map.Tree.lookupList key ys)))
  | m, Nil =>
    match c: Map.Raw.get key m with
      | None => rfl
      | Some value => rfl
  | m, Cons (kk, vv) rest =>
    rewrite Map.Raw.getFoldRemove key (Map.Raw.remove kk m) rest in
    match e: Ord.compare key kk with
      | Equal =>
        let gone: Map.Raw.get key (Map.Raw.remove kk m) = None := rewrite ord.equal key kk e in Map.Raw.getRemove kk m
        rewrite gone in
        match c: Map.Raw.get key m with
          | None => rfl
          | Some value => rfl
      | Less => rewrite Map.Raw.getRemoveOther kk key (Map.Spec.notEqualOfCompare key kk (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) m in rfl
      | Greater => rewrite Map.Raw.getRemoveOther kk key (Map.Spec.notEqualOfCompare key kk (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) m in rfl

-- What `get` finds after each.

theorem Map.Raw.getUnionWith [auto ord: Ord k] (a: Map.Raw k v) (key: k) (b: Map.Raw k v) (f: v → v → v):
    Map.Raw.get key (Map.Raw.unionWith f a b) = Option.merge (Map.Raw.get key a) (Map.Raw.get key b) f :=
  rewrite Map.Raw.getToList key a, Map.Raw.getToList key b in
  Eq.trans (Map.Raw.getToList key (Map.Raw.unionWith f a b))
    (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.Raw.toListUnionWith f a b))
      (Eq.trans
        (Map.Spec.lookupMerge (key2 x y => Some (f x y)) (key2 x => Some x) (key2 y => Some y) key None (Map.Raw.toList a) (Map.Raw.toList b)
          (Map.Raw.toListSorted a) (Map.Raw.toListSorted b))
        (Map.Spec.mergeAtUnionWith f key (Map.Tree.lookupList key (Map.Raw.toList a)) (Map.Tree.lookupList key (Map.Raw.toList b)))))

theorem Map.Raw.getIntersectWith [auto ord: Ord k] (a: Map.Raw k v) (key: k) (b: Map.Raw k w) (f: v → w → x):
    Map.Raw.get key (Map.Raw.intersectWith f a b) = Option.flatMap (Map.Raw.get key a) (value => Option.map (Map.Raw.get key b) (f value)) :=
  rewrite Map.Raw.getToList key a, Map.Raw.getToList key b in
  Eq.trans (Map.Raw.getToList key (Map.Raw.intersectWith f a b))
    (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.Raw.toListIntersectWith f a b))
      (Eq.trans
        (Map.Spec.lookupMerge (key2 x y => Some (f x y)) (key2 x => None) (key2 y => None) key None (Map.Raw.toList a) (Map.Raw.toList b)
          (Map.Raw.toListSorted a) (Map.Raw.toListSorted b))
        (Map.Spec.mergeAtIntersectWith f key (Map.Tree.lookupList key (Map.Raw.toList a)) (Map.Tree.lookupList key (Map.Raw.toList b)))))

theorem Map.Raw.getDifference [auto ord: Ord k] (a: Map.Raw k v) (key: k) (b: Map.Raw k w):
    Map.Raw.get key (Map.Raw.difference a b) = Option.filter (Map.Raw.get key a) (value => ¬(Map.Raw.contains key b)) :=
  rewrite Map.Raw.containsIsSome key b, Map.Raw.getToList key a, Map.Raw.getToList key b in
  Eq.trans (Map.Raw.getToList key (Map.Raw.difference a b))
    (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.Raw.toListDifference a b))
      (Eq.trans
        (Map.Spec.lookupMerge (key2 x y => None) (key2 x => Some x) (key2 y => None) key None (Map.Raw.toList a) (Map.Raw.toList b)
          (Map.Raw.toListSorted a) (Map.Raw.toListSorted b))
        (Map.Spec.mergeAtDifference key (Map.Tree.lookupList key (Map.Raw.toList a)) (Map.Tree.lookupList key (Map.Raw.toList b)))))

theorem Map.Raw.getMapMaybe [auto ord: Ord k] (m: Map.Raw k v) (key: k) (f: k → v → Option w):
    Map.Raw.get key (Map.Raw.mapMaybe f m) = Option.flatMap (Map.Raw.get key m) (f key) :=
  Eq.trans (Map.Raw.getToList key (Map.Raw.mapMaybe f m))
    (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.Raw.toListMapMaybe f m))
      (Eq.trans (Map.Spec.lookupMapMaybe f key None (Map.Raw.toList m) (Map.Raw.toListSorted m))
        (Eq.cong (.flatMap (f key)) (Eq.sym (Map.Raw.getToList key m)))))

-- Equivalent raw maps: the same entries, whatever their trees' shapes

def Map.Raw.Equiv (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]): Prop := Map.Raw.toList m = Map.Raw.toList n

theorem Map.Raw.equivRefl (m: Map.Raw k v [ord := o]): Map.Raw.Equiv m m := rfl

theorem Map.Raw.equivSym (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]) (h: Map.Raw.Equiv m n): Map.Raw.Equiv n m := Eq.sym h

theorem Map.Raw.equivTrans (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]) (p: Map.Raw k v [ord := o])
    (h1: Map.Raw.Equiv m n) (h2: Map.Raw.Equiv n p): Map.Raw.Equiv m p :=
  Eq.trans h1 h2

-- The same `get` for every key means the same entries; with
-- `Map.Raw.getRespects`, `Map.Raw.Equiv` is exactly "the same `get` everywhere".
theorem Map.Raw.equivOfGet [auto ord: Ord k] (m: Map.Raw k v) (n: Map.Raw k v) (h: (key: k) → Map.Raw.get key m = Map.Raw.get key n):
    Map.Raw.Equiv m n :=
  Map.Spec.extLookup None (Map.Raw.toList m) (Map.Raw.toList n) (Map.Raw.toListSorted m) (Map.Raw.toListSorted n)
    (key => Eq.trans (Eq.sym (Map.Raw.getToList key m)) (Eq.trans (h key) (Map.Raw.getToList key n)))

-- Each operation respects `Map.Raw.Equiv`: equivalent maps give equal results,
-- or equivalent maps.

theorem Map.Raw.getRespects [auto ord: Ord k] (key: k) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n):
    Map.Raw.get key m = Map.Raw.get key n :=
  Eq.trans (Map.Raw.getToList key m) (Eq.trans (Eq.cong (Map.Tree.lookupList key) h) (Eq.sym (Map.Raw.getToList key n)))

theorem Map.Raw.getOrRespects [auto ord: Ord k] (key: k) (d: v) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n):
    Map.Raw.getOr m key d = Map.Raw.getOr n key d :=
  Eq.cong (.getOrElse d) (Map.Raw.getRespects key m n h)

theorem Map.Raw.containsRespects [auto ord: Ord k] (key: k) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n):
    Map.Raw.contains key m = Map.Raw.contains key n :=
  rewrite Map.Raw.getRespects key m n h in rfl

theorem Map.Raw.sizeRespects (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]) (h: Map.Raw.Equiv m n): Map.Raw.size m = Map.Raw.size n :=
  Eq.trans (Map.Raw.sizeToList m) (Eq.trans (Eq.cong List.length h) (Eq.sym (Map.Raw.sizeToList n)))

theorem Map.Raw.isEmptyRespects (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]) (h: Map.Raw.Equiv m n): Map.Raw.isEmpty m = Map.Raw.isEmpty n :=
  Eq.cong (s => Nat.equal s 0) (Map.Raw.sizeRespects m n h)

theorem Map.Raw.keysRespects (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]) (h: Map.Raw.Equiv m n): Map.Raw.keys m = Map.Raw.keys n :=
  Eq.cong (.map Pair.fst) h

theorem Map.Raw.valuesRespects (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]) (h: Map.Raw.Equiv m n): Map.Raw.values m = Map.Raw.values n :=
  Eq.cong (.map Pair.snd) h

theorem Map.Raw.foldLeftRespects (f: b → k → v → b) (z: b) (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]) (h: Map.Raw.Equiv m n):
    Map.Raw.foldLeft f z m = Map.Raw.foldLeft f z n :=
  Eq.trans (Map.Raw.foldLeftToList f z m) (Eq.trans (Eq.cong (Map.Spec.foldLeft f z) h) (Eq.sym (Map.Raw.foldLeftToList f z n)))

theorem Map.Raw.insertWithRespects [auto ord: Ord k] (f: v → v → v) (key: k) (value: v) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n):
    Map.Raw.Equiv (Map.Raw.insertWith f key value m) (Map.Raw.insertWith f key value n) :=
  Eq.trans (Map.Raw.toListInsertWith f key value m)
    (Eq.trans (Eq.cong (Map.Spec.insertWith f key value) h) (Eq.sym (Map.Raw.toListInsertWith f key value n)))

theorem Map.Raw.insertRespects [auto ord: Ord k] (key: k) (value: v) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n):
    Map.Raw.Equiv (Map.Raw.insert key value m) (Map.Raw.insert key value n) :=
  Map.Raw.insertWithRespects (new old => new) key value m n h

theorem Map.Raw.removeRespects [auto ord: Ord k] (key: k) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n):
    Map.Raw.Equiv (Map.Raw.remove key m) (Map.Raw.remove key n) :=
  Eq.trans (Map.Raw.toListRemove key m) (Eq.trans (Eq.cong (Map.Spec.remove key) h) (Eq.sym (Map.Raw.toListRemove key n)))

theorem Map.Raw.alterRespects [auto ord: Ord k] (f: Option v → Option v) (key: k) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n):
    Map.Raw.Equiv (Map.Raw.alter f key m) (Map.Raw.alter f key n) :=
  Eq.trans (Map.Raw.toListAlter f key m) (Eq.trans (Eq.cong (Map.Spec.alter f key) h) (Eq.sym (Map.Raw.toListAlter f key n)))

theorem Map.Raw.adjustRespects [auto ord: Ord k] (f: v → v) (key: k) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n):
    Map.Raw.Equiv (Map.Raw.adjust f key m) (Map.Raw.adjust f key n) :=
  Eq.trans (Map.Raw.toListAdjust f key m) (Eq.trans (Eq.cong (Map.Spec.adjust f key) h) (Eq.sym (Map.Raw.toListAdjust f key n)))

theorem Map.Raw.mapRespects (f: v → w) (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]) (h: Map.Raw.Equiv m n):
    Map.Raw.Equiv (Map.Raw.map f m) (Map.Raw.map f n) :=
  Eq.trans (Map.Raw.toListMap f m) (Eq.trans (Eq.cong (Map.Spec.mapValues f) h) (Eq.sym (Map.Raw.toListMap f n)))

theorem Map.Raw.filterRespects [auto ord: Ord k] (p: k → v → Bool) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n):
    Map.Raw.Equiv (Map.Raw.filter p m) (Map.Raw.filter p n) :=
  Eq.trans (Map.Raw.toListFilter p m) (Eq.trans (Eq.cong (Map.Spec.filter p) h) (Eq.sym (Map.Raw.toListFilter p n)))

theorem Map.Raw.unionRespects [auto ord: Ord k] (a: Map.Raw k v) (a2: Map.Raw k v) (b: Map.Raw k v) (b2: Map.Raw k v)
    (ha: Map.Raw.Equiv a a2) (hb: Map.Raw.Equiv b b2): Map.Raw.Equiv (Map.Raw.union a b) (Map.Raw.union a2 b2) :=
  Eq.trans (Map.Raw.toListUnion a b)
    (Eq.trans (Eq.cong (l => Map.Spec.union l (Map.Raw.toList b)) ha)
      (Eq.trans (Eq.cong (l => Map.Spec.union (Map.Raw.toList a2) l) hb) (Eq.sym (Map.Raw.toListUnion a2 b2))))

theorem Map.Raw.unionWithRespects [auto ord: Ord k] (f: v → v → v) (a: Map.Raw k v) (a2: Map.Raw k v) (b: Map.Raw k v) (b2: Map.Raw k v)
    (ha: Map.Raw.Equiv a a2) (hb: Map.Raw.Equiv b b2): Map.Raw.Equiv (Map.Raw.unionWith f a b) (Map.Raw.unionWith f a2 b2) :=
  Eq.trans (Map.Raw.toListUnionWith f a b)
    (Eq.trans (Eq.cong (l => Map.Spec.unionWith f l (Map.Raw.toList b)) ha)
      (Eq.trans (Eq.cong (l => Map.Spec.unionWith f (Map.Raw.toList a2) l) hb) (Eq.sym (Map.Raw.toListUnionWith f a2 b2))))

theorem Map.Raw.intersectWithRespects [auto ord: Ord k] (f: v → w → x) (a: Map.Raw k v) (a2: Map.Raw k v) (b: Map.Raw k w) (b2: Map.Raw k w)
    (ha: Map.Raw.Equiv a a2) (hb: Map.Raw.Equiv b b2): Map.Raw.Equiv (Map.Raw.intersectWith f a b) (Map.Raw.intersectWith f a2 b2) :=
  Eq.trans (Map.Raw.toListIntersectWith f a b)
    (Eq.trans (Eq.cong (l => Map.Spec.intersectWith f l (Map.Raw.toList b)) ha)
      (Eq.trans (Eq.cong (l => Map.Spec.intersectWith f (Map.Raw.toList a2) l) hb) (Eq.sym (Map.Raw.toListIntersectWith f a2 b2))))

theorem Map.Raw.differenceRespects [auto ord: Ord k] (a: Map.Raw k v) (a2: Map.Raw k v) (b: Map.Raw k w) (b2: Map.Raw k w)
    (ha: Map.Raw.Equiv a a2) (hb: Map.Raw.Equiv b b2): Map.Raw.Equiv (Map.Raw.difference a b) (Map.Raw.difference a2 b2) :=
  Eq.trans (Map.Raw.toListDifference a b)
    (Eq.trans (Eq.cong (l => Map.Spec.difference l (Map.Raw.toList b)) ha)
      (Eq.trans (Eq.cong (l => Map.Spec.difference (Map.Raw.toList a2) l) hb) (Eq.sym (Map.Raw.toListDifference a2 b2))))

theorem Map.Raw.mapMaybeRespects [auto ord: Ord k] (f: k → v → Option w) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n):
    Map.Raw.Equiv (Map.Raw.mapMaybe f m) (Map.Raw.mapMaybe f n) :=
  Eq.trans (Map.Raw.toListMapMaybe f m) (Eq.trans (Eq.cong (Map.Spec.mapMaybe f) h) (Eq.sym (Map.Raw.toListMapMaybe f n)))

theorem Map.Raw.minRespects (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]) (h: Map.Raw.Equiv m n): Map.Raw.min m = Map.Raw.min n :=
  Eq.trans (Map.Raw.minToList m) (Eq.trans (Eq.cong List.head h) (Eq.sym (Map.Raw.minToList n)))

theorem Map.Raw.maxRespects (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]) (h: Map.Raw.Equiv m n): Map.Raw.max m = Map.Raw.max n :=
  Eq.trans (Map.Raw.maxToList m) (Eq.trans (Eq.cong List.last h) (Eq.sym (Map.Raw.maxToList n)))

theorem Map.Raw.belowRespects [auto ord: Ord k] (key: k) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n): Map.Raw.below key m = Map.Raw.below key n :=
  Eq.trans (Map.Raw.belowToList m key)
    (Eq.trans (Eq.cong (xs => List.last (List.filter xs (e => Map.Spec.isLess e.fst key))) h) (Eq.sym (Map.Raw.belowToList n key)))

theorem Map.Raw.aboveRespects [auto ord: Ord k] (key: k) (m: Map.Raw k v) (n: Map.Raw k v) (h: Map.Raw.Equiv m n): Map.Raw.above key m = Map.Raw.above key n :=
  Eq.trans (Map.Raw.aboveToList m key)
    (Eq.trans (Eq.cong (.find ((e: (k, v)) => Map.Spec.isLess key e.fst)) h) (Eq.sym (Map.Raw.aboveToList n key)))

theorem Map.Raw.mapWithKeyRespects (f: k → v → w) (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]) (h: Map.Raw.Equiv m n):
    Map.Raw.Equiv (Map.Raw.mapWithKey f m) (Map.Raw.mapWithKey f n) :=
  Eq.trans (Map.Raw.toListMapWithKey f m) (Eq.trans (Eq.cong (Map.Spec.mapWithKey f) h) (Eq.sym (Map.Raw.toListMapWithKey f n)))

-- Folds whose steps agree give the same result; so `filter` with
-- predicates that agree keeps the same entries.
theorem Map.Spec.foldLeftCong (f1: b → k → v → b) (f2: b → k → v → b):
    (z: b) → (xs: List (k, v)) → ((acc: b) → (key: k) → (value: v) → f1 acc key value = f2 acc key value) →
    Map.Spec.foldLeft f1 z xs = Map.Spec.foldLeft f2 z xs
  | z, Nil, h => rfl
  | z, Cons (kk, vv) rest, h =>
    Eq.trans (Map.Spec.foldLeftCong f1 f2 (f1 z kk vv) rest h) (Eq.cong (y => Map.Spec.foldLeft f2 y rest) (h z kk vv))

theorem Map.Raw.filterCongEquiv [auto ord: Ord k] (p: k → v → Bool) (q: k → v → Bool)
    (same: (key: k) → (value: v) → p key value = q key value) (m: Map.Raw k v):
    Map.Raw.Equiv (Map.Raw.filter p m) (Map.Raw.filter q m) :=
  Eq.trans (Map.Raw.toListFilter p m)
    (Eq.trans (Map.Spec.foldLeftCong
        ((l: List (k, v)) (key: k) (value: v) => if p key value then Map.Spec.insert key value l else l)
        ((l: List (k, v)) (key: k) (value: v) => if q key value then Map.Spec.insert key value l else l)
        Nil (Map.Raw.toList m) (l key value => rewrite same key value in rfl))
      (Eq.sym (Map.Raw.toListFilter q m)))

-- Deciding `Map.Raw.Equiv` by comparing the entry lists. It needs `DecEq` for
-- the values (the keys have one in their `Ord`): a test that said "same"
-- exactly when the entries are equal would decide equality of any two
-- values, through one-entry maps.
def Map.Raw.same [auto dv: DecEq v] (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]): Bool :=
  Map.Raw.toList m == Map.Raw.toList n

theorem Map.Raw.sameSound [auto dv: DecEq v] (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o])
    (h: Map.Raw.same m n = True): Map.Raw.Equiv m n :=
  Decidable.toBoolSound (DecEq.decide (Map.Raw.toList m) (Map.Raw.toList n)) h

theorem Map.Raw.sameComplete [auto dv: DecEq v] (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o])
    (h: Map.Raw.Equiv m n): Map.Raw.same m n = True :=
  Decidable.toBoolOf (DecEq.decide (Map.Raw.toList m) (Map.Raw.toList n)) h

theorem Map.Raw.sameIff [auto dv: DecEq v] (m: Map.Raw k v [ord := o]) (n: Map.Raw k v [ord := o]):
    Iff (Map.Raw.same m n = True) (Map.Raw.Equiv m n) :=
  { forward = Map.Raw.sameSound m n, backward = Map.Raw.sameComplete m n }

def Map.Spec.example: List (Nat, Text) := [(1, "a"), (3, "c")]

test "map spec: insert" :=
  Map.Spec.insert 2 "b" Map.Spec.example == [(1, "a"), (2, "b"), (3, "c")]
    ∧ Map.Spec.insert 3 "C" Map.Spec.example == [(1, "a"), (3, "C")]
    ∧ Map.Spec.insert 4 "d" Map.Spec.example == [(1, "a"), (3, "c"), (4, "d")]
test "map spec: remove" :=
  Map.Spec.remove 1 Map.Spec.example == [(3, "c")] ∧ Map.Spec.remove 2 Map.Spec.example == Map.Spec.example
test "map spec: fromList, later wins" := Map.Spec.fromList [(2, "x"), (1, "a"), (2, "b")] == [(1, "a"), (2, "b")]
test "raw map: same in any order" :=
  Map.Raw.same (Map.Raw.fromList [(1, "a"), (2, "b"), (3, "c")]: Map.Raw Nat Text) (Map.Raw.fromList [(3, "c"), (1, "a"), (2, "b")])
test "raw map: same sees a changed value" :=
  ¬(Map.Raw.same (Map.Raw.fromList [(1, "a"), (2, "b")]: Map.Raw Nat Text) (Map.Raw.fromList [(1, "a"), (2, "B")]))

def Map.Raw.example9: Map.Raw Nat Nat := Map.Raw.fromList [(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60), (7, 70), (8, 80), (9, 90)]

test "raw map: filter" := Map.Raw.keys (Map.Raw.filter (key t => Nat.leq 2 key) Map.Raw.example) == [2, 3]
test "raw map: filter keeps none, or all" :=
  Map.Raw.isEmpty (Map.Raw.filter (key t => False) Map.Raw.example)
    ∧ Map.Raw.toList (Map.Raw.filter (key t => True) Map.Raw.example) == Map.Raw.toList Map.Raw.example
test "raw map: union" := Map.Raw.toList (Map.Raw.union (Map.Raw.singleton 1 "x") Map.Raw.example) == [(1, "x"), (2, "b"), (3, "c")]
test "raw map: mapMaybe" :=
  Map.Raw.toList (Map.Raw.mapMaybe (key value => if Nat.leq 2 key then Some (key * 2) else None) Map.Raw.example) == [(2, 4), (3, 6)]
-- Each way of combining: inserting or removing a much smaller map's entries,
-- whichever side it is, and merging the entry lists.
test "raw map: unionWith, small first map, small second map and merged" :=
  Map.Raw.toList (Map.Raw.unionWith Nat.sub (Map.Raw.singleton 3 100) Map.Raw.example9)
      == [(1, 10), (2, 20), (3, 70), (4, 40), (5, 50), (6, 60), (7, 70), (8, 80), (9, 90)]
    ∧ Map.Raw.toList (Map.Raw.unionWith Nat.sub Map.Raw.example9 (Map.Raw.singleton 3 1))
      == [(1, 10), (2, 20), (3, 29), (4, 40), (5, 50), (6, 60), (7, 70), (8, 80), (9, 90)]
    ∧ Map.Raw.toList (Map.Raw.unionWith Nat.sub Map.Raw.example9 (Map.Raw.fromList [(3, 1), (12, 5)]))
      == [(1, 10), (2, 20), (3, 29), (4, 40), (5, 50), (6, 60), (7, 70), (8, 80), (9, 90), (12, 5)]
test "raw map: intersectWith, small first map and merged" :=
  Map.Raw.toList (Map.Raw.intersectWith Nat.sub (Map.Raw.fromList [(3, 100), (12, 1)]: Map.Raw Nat Nat) Map.Raw.example9) == [(3, 70)]
    ∧ Map.Raw.toList (Map.Raw.intersectWith Nat.sub Map.Raw.example9 (Map.Raw.fromList [(3, 1), (12, 1)])) == [(3, 29)]
test "raw map: difference, small first map, small second map and merged" :=
  Map.Raw.keys (Map.Raw.difference (Map.Raw.fromList [(3, 100), (12, 1)]: Map.Raw Nat Nat) Map.Raw.example9) == [12]
    ∧ Map.Raw.keys (Map.Raw.difference Map.Raw.example9 (Map.Raw.fromList [(3, 1), (12, 1)])) == [1, 2, 4, 5, 6, 7, 8, 9]
    ∧ Map.Raw.keys (Map.Raw.difference Map.Raw.example9 (Map.Raw.singleton 3 1)) == [1, 2, 4, 5, 6, 7, 8, 9]
    ∧ Map.Raw.keys (Map.Raw.difference Map.Raw.example9 (Map.Raw.singleton 12 1)) == [1, 2, 3, 4, 5, 6, 7, 8, 9]
test "raw map: fromListFast, ascending or not" :=
  Map.Spec.isAscending None [(1, "a"), (2, "b"), (5, "e")] ∧ ¬(Map.Spec.isAscending None [(1, "a"), (1, "b")])
    ∧ ¬(Map.Spec.isAscending None [(2, "b"), (1, "a")])
    ∧ Map.Raw.toList (Map.Raw.fromListFast [(1, "a"), (2, "b"), (5, "e")]) == [(1, "a"), (2, "b"), (5, "e")]
    ∧ Map.Raw.toList (Map.Raw.fromListFast [(1, "a"), (1, "b"), (0, "z")]) == [(0, "z"), (1, "b")]
    ∧ Map.Raw.isEmpty (Map.Raw.fromListFast (Nil: List (Nat, Text)))
test "raw map: fromSorted builds every size" :=
  List.all [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    (n => Map.Raw.keys (Map.Raw.filter (key t => Nat.leq key n) Map.Raw.example9) == List.filter [1, 2, 3, 4, 5, 6, 7, 8, 9] (key => Nat.leq key n))
