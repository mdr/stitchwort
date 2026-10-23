-- What each `Map` operation does to the entries in key order (`Map.toList`),
-- stated with sorted association lists (`Map.Spec`), and `Map.Equiv`: two
-- maps are equivalent when they have the same entries, whatever their trees'
-- shapes. Each operation respects `Map.Equiv`, proved from its agreement
-- lemma; `Map.same` decides it. Stage 0 of docs/proposals/map-equality.md
-- ("Stage 0 results" lists what is and isn't proved).

import Std (Eq)
import Map.Tree (Tip, Bin)

-- Sorted association lists

-- A map's entries in key order, as a list: what the functions below act on.
-- (A type of its own, so that `Map.Spec` belongs to this file, and a dot
-- call such as `xs.filter` on a list doesn't load it.)
type Map.Spec (k: Type) (v: Type) = List (k, v)

-- `value` at `key` in a list sorted by key, as `Map.insertWith` does it:
-- before the first larger key, or combined with the value at an equal key.
def Map.Spec.insertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v): List (k, v) -> List (k, v)
  | Nil => Cons (key, value) Nil
  | Cons (kk, vv) rest => match Ord.compare key kk with
    | Less => Cons (key, value) (Cons (kk, vv) rest)
    | Equal => Cons (kk, f value vv) rest
    | Greater => Cons (kk, vv) (Map.Spec.insertWith f key value rest)

def Map.Spec.insert [auto ord: Ord k] (key: k) (value: v) (xs: List (k, v)): List (k, v) :=
  Map.Spec.insertWith (new old => new) key value xs

-- Without the entry at `key`.
def Map.Spec.remove [auto ord: Ord k] (key: k): List (k, v) -> List (k, v)
  | Nil => Nil
  | Cons (kk, vv) rest => match Ord.compare key kk with
    | Less => Cons (kk, vv) rest
    | Equal => rest
    | Greater => Cons (kk, vv) (Map.Spec.remove key rest)

-- Every value changed by `f`.
def Map.Spec.mapValues (f: v -> w): List (k, v) -> List (k, w)
  | Nil => Nil
  | Cons (kk, vv) rest => Cons (kk, f vv) (Map.Spec.mapValues f rest)

-- Left fold over the entries: `f (f z k1 v1) k2 v2`.
def Map.Spec.foldLeft (f: b -> k -> v -> b): b -> List (k, v) -> b
  | z, Nil => z
  | z, Cons (kk, vv) rest => Map.Spec.foldLeft f (f z kk vv) rest

-- The pairs inserted in turn into an empty list; a later pair wins.
def Map.Spec.fromList [auto ord: Ord k] (xs: List (k, v)): List (k, v) :=
  List.foldLeft (l entry => Map.Spec.insert entry.fst entry.snd l) Nil xs

-- What `Map.filter` does: the entries for which `p` holds, inserted in turn.
def Map.Spec.filter [auto ord: Ord k] (p: k -> v -> Bool) (xs: List (k, v)): List (k, v) :=
  Map.Spec.foldLeft (l key value => if p key value then Map.Spec.insert key value l else l) Nil xs

-- What `Map.union` does: `a`'s entries inserted into `b`'s, so `a`'s values win.
def Map.Spec.union [auto ord: Ord k] (a: List (k, v)) (b: List (k, v)): List (k, v) :=
  Map.Spec.foldLeft (l key value => Map.Spec.insert key value l) b a

-- What `Map.alter` does.
def Map.Spec.alter [auto ord: Ord k] (f: Option v -> Option v) (key: k) (xs: List (k, v)): List (k, v) :=
  match f (Map.Tree.lookupList key xs) with
    | None => Map.Spec.remove key xs
    | Some value => Map.Spec.insert key value xs

-- What `Map.adjust` does.
def Map.Spec.adjust [auto ord: Ord k] (f: v -> v) (key: k) (xs: List (k, v)): List (k, v) :=
  match Map.Tree.lookupList key xs with
    | None => xs
    | Some old => Map.Spec.insert key (f old) xs

-- `key` is below the list's first key (or the list is empty).
def Map.Spec.BelowHead (ord: Ord k) (key: k): List (k, v) -> Prop
  | Nil => Unit
  | Cons (kk, vv) rest => Ord.compare key kk = Less

-- One step of each, at a smaller, equal or larger first key.

theorem Map.Spec.insertWithLess [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (kk: k) (vv: v) (rest: List (k, v))
    (e: Ord.compare key kk = Less):
    Map.Spec.insertWith f key value (Cons (kk, vv) rest) = Cons (key, value) (Cons (kk, vv) rest) :=
  rewrite e in rfl

theorem Map.Spec.insertWithEqual [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (kk: k) (vv: v) (rest: List (k, v))
    (e: Ord.compare key kk = Equal):
    Map.Spec.insertWith f key value (Cons (kk, vv) rest) = Cons (kk, f value vv) rest :=
  rewrite e in rfl

theorem Map.Spec.insertWithGreater [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (kk: k) (vv: v) (rest: List (k, v))
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
theorem Map.Tree.pastOnto [auto ord: Ord k] (g: List (k, v) -> List (k, v)) (key: k)
    (step: (kk: k) -> (vv: v) -> (rest: List (k, v)) -> Ord.compare key kk = Greater -> g (Cons (kk, vv) rest) = Cons (kk, vv) (g rest)):
    (lo: Option k) -> (hi: k) -> (t: Map.Tree k v) -> (ys: List (k, v)) ->
    Map.Tree.Within ord lo (Some hi) t -> Not (Ord.compare key hi = Less) ->
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

theorem Map.Tree.insertWithOnto [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v):
    (lo: Option k) -> (hi: Option k) -> (t: Map.Tree k v) -> (acc: List (k, v)) ->
    Map.Tree.Within ord lo hi t -> Map.Spec.BelowHead ord key acc ->
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
theorem Map.Tree.deleteMinOnto: (l: Map.Tree k v) -> (key: k) -> (value: v) -> (r: Map.Tree k v) -> (acc: List (k, v)) ->
    Cons (Map.Tree.minKey key l, Map.Tree.minValue value l) (Map.Tree.toListOnto (Map.Tree.deleteMin l key value r) acc)
      = Map.Tree.toListOnto l (Cons (key, value) (Map.Tree.toListOnto r acc))
  | Tip, key, value, r, acc => rfl
  | Bin s ll lk lv lr, key, value, r, acc =>
    Eq.trans (Eq.cong (zs => Cons (Map.Tree.minKey lk ll, Map.Tree.minValue lv ll) zs)
        (Map.Tree.balanceOnto (Map.Tree.deleteMin ll lk lv lr) key value r acc))
      (Map.Tree.deleteMinOnto ll lk lv lr (Cons (key, value) (Map.Tree.toListOnto r acc)))

theorem Map.Tree.glueOnto: (l: Map.Tree k v) -> (r: Map.Tree k v) -> (acc: List (k, v)) ->
    Map.Tree.toListOnto (Map.Tree.glue l r) acc = Map.Tree.toListOnto l (Map.Tree.toListOnto r acc)
  | Tip, r, acc => rfl
  | Bin s ll lk lv lr, Tip, acc => rfl
  | Bin s ll lk lv lr, Bin s2 rl rk rv rr, acc =>
    Eq.trans (Map.Tree.balanceOnto (Bin s ll lk lv lr) (Map.Tree.minKey rk rl) (Map.Tree.minValue rv rl) (Map.Tree.deleteMin rl rk rv rr) acc)
      (Eq.cong (zs => Map.Tree.toListOnto (Bin s ll lk lv lr) zs) (Map.Tree.deleteMinOnto rl rk rv rr acc))

theorem Map.Tree.removeOnto [auto ord: Ord k] (key: k):
    (lo: Option k) -> (hi: Option k) -> (t: Map.Tree k v) -> (acc: List (k, v)) ->
    Map.Tree.Within ord lo hi t -> Map.Spec.BelowHead ord key acc ->
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

theorem Map.Tree.mapOnto (f: v -> w): (t: Map.Tree k v) -> (acc: List (k, v)) ->
    Map.Tree.toListOnto (Map.Tree.map f t) (Map.Spec.mapValues f acc) = Map.Spec.mapValues f (Map.Tree.toListOnto t acc)
  | Tip, acc => rfl
  | Bin s l kk vv r, acc =>
    Eq.trans (Eq.cong (zs => Map.Tree.toListOnto (Map.Tree.map f l) (Cons (kk, f vv) zs)) (Map.Tree.mapOnto f r acc))
      (Map.Tree.mapOnto f l (Cons (kk, vv) (Map.Tree.toListOnto r acc)))

theorem Map.Tree.foldLeftOnto (f: b -> k -> v -> b): (z: b) -> (t: Map.Tree k v) -> (acc: List (k, v)) ->
    Map.Spec.foldLeft f z (Map.Tree.toListOnto t acc) = Map.Spec.foldLeft f (Map.Tree.foldLeft f z t) acc
  | z, Tip, acc => rfl
  | z, Bin s l kk vv r, acc =>
    Eq.trans (Map.Tree.foldLeftOnto f z l (Cons (kk, vv) (Map.Tree.toListOnto r acc)))
      (Map.Tree.foldLeftOnto f (f (Map.Tree.foldLeft f z l) kk vv) r acc)

-- With the stored sizes right, a tree has `size` entries.
theorem Map.Tree.lengthOnto: (t: Map.Tree k v) -> (acc: List (k, v)) -> Map.Tree.Sized t ->
    List.length (Map.Tree.toListOnto t acc) = Map.Tree.size t + List.length acc
  | Tip, acc, st => rfl
  | Bin s l kk vv r, acc, Both e (Both sl sr) =>
    Eq.trans (Map.Tree.lengthOnto l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) sl)
      (Eq.trans (Eq.cong (n => Map.Tree.size l + Succ n) (Map.Tree.lengthOnto r acc sr))
        (Eq.trans (Nat.addSucc (Map.Tree.size l) (Map.Tree.size r + List.length acc))
          (Eq.trans (Eq.cong Succ (Eq.sym (Nat.addAssoc (Map.Tree.size l) (Map.Tree.size r) (List.length acc))))
            (Eq.cong (n => n + List.length acc) (Eq.sym e)))))

-- The same for maps.

theorem Map.toListEmpty [auto ord: Ord k]: Map.toList (Map.empty: Map k v) = Nil := rfl

theorem Map.toListInsertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (m: Map k v):
    Map.toList (Map.insertWith f key value m) = Map.Spec.insertWith f key value (Map.toList m) :=
  Map.Tree.insertWithOnto f key value None None m.tree Nil m.ordered Trivial

theorem Map.toListInsert [auto ord: Ord k] (key: k) (value: v) (m: Map k v):
    Map.toList (Map.insert key value m) = Map.Spec.insert key value (Map.toList m) :=
  Map.toListInsertWith (new old => new) key value m

theorem Map.toListSingleton [auto ord: Ord k] (key: k) (value: v):
    Map.toList (Map.singleton key value: Map k v) = [(key, value)] := rfl

theorem Map.toListRemove [auto ord: Ord k] (key: k) (m: Map k v):
    Map.toList (Map.remove key m) = Map.Spec.remove key (Map.toList m) :=
  Map.Tree.removeOnto key None None m.tree Nil m.ordered Trivial

theorem Map.toListMap (f: v -> w) (m: Map k v [ord := o]):
    Map.toList (Map.map f m) = Map.Spec.mapValues f (Map.toList m) :=
  Map.Tree.mapOnto f m.tree Nil

theorem Map.foldLeftToList (f: b -> k -> v -> b) (z: b) (m: Map k v [ord := o]):
    Map.foldLeft f z m = Map.Spec.foldLeft f z (Map.toList m) :=
  Eq.sym (Map.Tree.foldLeftOnto f z m.tree Nil)

theorem Map.getToList [auto ord: Ord k] (key: k) (m: Map k v):
    Map.get key m = Map.Tree.lookupList key (Map.toList m) :=
  Map.Tree.getLookup key None None m.tree m.ordered

theorem Map.sizeToList (m: Map k v [ord := o]): Map.size m = List.length (Map.toList m) :=
  Eq.sym (Eq.trans (Map.Tree.lengthOnto m.tree Nil m.sized) (Nat.addZero (Map.Tree.size m.tree)))

-- A fold whose step agrees with a list step gives the list fold's entries.
theorem Map.toListFold [auto ord: Ord k] (g: Map k v -> k -> v -> Map k v) (h: List (k, v) -> k -> v -> List (k, v))
    (step: (m: Map k v) -> (key: k) -> (value: v) -> Map.toList (g m key value) = h (Map.toList m) key value):
    (m: Map k v) -> (xs: List (k, v)) -> Map.toList (Map.Spec.foldLeft g m xs) = Map.Spec.foldLeft h (Map.toList m) xs
  | m, Nil => rfl
  | m, Cons (kk, vv) rest =>
    Eq.trans (Map.toListFold g h step (g m kk vv) rest)
      (Eq.cong (l => Map.Spec.foldLeft h l rest) (step m kk vv))

theorem Map.toListFromListOnto [auto ord: Ord k]: (xs: List (k, v)) -> (m: Map k v) ->
    Map.toList (List.foldLeft (acc entry => Map.insert entry.fst entry.snd acc) m xs)
      = List.foldLeft (l entry => Map.Spec.insert entry.fst entry.snd l) (Map.toList m) xs
  | Nil, m => rfl
  | Cons (kk, vv) rest, m =>
    Eq.trans (Map.toListFromListOnto rest (Map.insert kk vv m))
      (Eq.cong (l => List.foldLeft (l2 entry => Map.Spec.insert entry.fst entry.snd l2) l rest) (Map.toListInsert kk vv m))

theorem Map.toListFromList [auto ord: Ord k] (xs: List (k, v)):
    Map.toList (Map.fromList xs: Map k v) = Map.Spec.fromList xs :=
  Map.toListFromListOnto xs Map.empty

theorem Map.toListFilterStep [auto ord: Ord k] (p: k -> v -> Bool) (m: Map k v) (key: k) (value: v):
    Map.toList (if p key value then Map.insert key value m else m)
      = (if p key value then Map.Spec.insert key value (Map.toList m) else Map.toList m) :=
  match c: p key value with
    | True => Map.toListInsert key value m
    | False => rfl

theorem Map.toListFilter [auto ord: Ord k] (p: k -> v -> Bool) (m: Map k v):
    Map.toList (Map.filter p m) = Map.Spec.filter p (Map.toList m) :=
  rewrite Map.foldLeftToList (acc key value => if p key value then Map.insert key value acc else acc) Map.empty m in
  Map.toListFold (acc key value => if p key value then Map.insert key value acc else acc)
    (l key value => if p key value then Map.Spec.insert key value l else l)
    (Map.toListFilterStep p) Map.empty (Map.toList m)

theorem Map.toListUnion [auto ord: Ord k] (a: Map k v) (b: Map k v):
    Map.toList (Map.union a b) = Map.Spec.union (Map.toList a) (Map.toList b) :=
  rewrite Map.foldLeftToList (acc key value => Map.insert key value acc) b a in
  Map.toListFold (acc key value => Map.insert key value acc) ((l: List (k, v)) (key: k) (value: v) => Map.Spec.insert key value l)
    (m key value => Map.toListInsert key value m) b (Map.toList a)

theorem Map.toListAlter [auto ord: Ord k] (f: Option v -> Option v) (key: k) (m: Map k v):
    Map.toList (Map.alter f key m) = Map.Spec.alter f key (Map.toList m) :=
  rewrite Map.getToList key m in
  match c: f (Map.Tree.lookupList key (Map.toList m)) with
    | None => Map.toListRemove key m
    | Some value => Map.toListInsert key value m

theorem Map.toListAdjust [auto ord: Ord k] (f: v -> v) (key: k) (m: Map k v):
    Map.toList (Map.adjust f key m) = Map.Spec.adjust f key (Map.toList m) :=
  rewrite Map.getToList key m in
  match c: Map.Tree.lookupList key (Map.toList m) with
    | None => rfl
    | Some old => Map.toListInsert key (f old) m

-- The entries are in strictly increasing key order

-- Every key is above `lo`, each above the one before.
def Map.Spec.Ascending (ord: Ord k): Option k -> List (k, v) -> Prop
  | lo, Nil => Unit
  | lo, Cons (kk, vv) rest => And (Map.Tree.Above ord lo kk) (Map.Spec.Ascending ord (Some kk) rest)

def Map.Spec.Sorted (ord: Ord k) (xs: List (k, v)): Prop := Map.Spec.Ascending ord None xs

-- The list can follow keys below `hi`: it's empty, or its first key isn't below `hi`.
def Map.Spec.Fits (ord: Ord k): Option k -> List (k, v) -> Prop
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

theorem Map.Spec.ascendingAbove (ord: Ord k) (lo: Option k) (kk: k): (hi: Option k) -> (acc: List (k, v)) ->
    Map.Tree.Below ord kk hi -> Map.Spec.Ascending ord lo acc -> Map.Spec.Fits ord hi acc ->
    Map.Spec.Ascending ord (Some kk) acc
  | hi, Nil, b, asc, fits => Trivial
  | None, Cons (a, x) rest, b, asc, fits => Void.exfalso fits
  | Some h, Cons (a, x) rest, b, Both aa arest, fits => Both (Map.Spec.lessOfLessLe ord kk h a b fits) arest

theorem Map.Tree.ascendingOnto (ord: Ord k): (lo: Option k) -> (hi: Option k) -> (t: Map.Tree k v) -> (acc: List (k, v)) ->
    Map.Tree.Within ord lo hi t -> Map.Spec.Ascending ord lo acc -> Map.Spec.Fits ord hi acc ->
    Map.Spec.Ascending ord lo (Map.Tree.toListOnto t acc)
  | lo, hi, Tip, acc, w, asc, fits => asc
  | lo, hi, Bin s l kk vv r, acc, Both (Both akk bkk) (Both wl wr), asc, fits =>
    Map.Tree.ascendingOnto ord lo (Some kk) l (Cons (kk, vv) (Map.Tree.toListOnto r acc)) wl
      (Both akk (Map.Tree.ascendingOnto ord (Some kk) hi r acc wr (Map.Spec.ascendingAbove ord lo kk hi acc bkk asc fits) fits))
      (x => Ordering.equalNotLess (Eq.trans (Eq.sym (Ord.compareSelf kk)) x))

theorem Map.toListSorted [auto ord: Ord k] (m: Map k v): Map.Spec.Sorted ord (Map.toList m) :=
  Map.Tree.ascendingOnto ord None None m.tree Nil m.ordered Trivial Trivial

-- In a list whose keys are all above `lo`, no key at or below `lo` is found.
theorem Map.Spec.lookupBelow [auto ord: Ord k] (key: k): (lo: k) -> (xs: List (k, v)) ->
    Map.Spec.Ascending ord (Some lo) xs -> Not (Ord.compare key lo = Greater) -> Map.Tree.lookupList key xs = None
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
    (same: (key: k) -> Map.Tree.lookupList key (Cons (a, x) xs) = Map.Tree.lookupList key (Cons (b, y) ys)) (key: k):
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
theorem Map.Spec.extLookup [auto ord: Ord k]: (lo: Option k) -> (xs: List (k, v)) -> (ys: List (k, v)) ->
    Map.Spec.Ascending ord lo xs -> Map.Spec.Ascending ord lo ys ->
    ((key: k) -> Map.Tree.lookupList key xs = Map.Tree.lookupList key ys) -> xs = ys
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
          Eq.cong (Option.getOrElse x)
            (Eq.trans (Eq.sym (Map.Spec.lookupHead a x xs)) (Eq.trans (same a) (Map.Spec.lookupEqualHead a b y ys c))),
          Map.Spec.extLookup (Some a) xs ys axs (rewrite ord.equal a b c in bys) (Map.Spec.tailsAgree a x xs b y ys c axs bys same) in
        rfl
      | Greater =>
        Void.exfalso (Option.noneNotSome y
          (Eq.trans (Eq.sym (Map.Spec.lookupAbsentHead b a x xs (Map.Tree.lessOfGreater ord a b c) axs))
            (Eq.trans (same b) (Map.Spec.lookupHead b y ys))))

-- So `filter` keeps the entries for which `p` holds, in order.

-- In a sorted list, a key is below every later one.
theorem Map.Spec.belowLater [auto ord: Ord k]: (c: k) -> (ys: List (k, v)) -> (a: k) -> (b: v) -> (rest: List (k, v)) ->
    Map.Spec.Ascending ord (Some c) (List.append ys (Cons (a, b) rest)) -> Ord.compare c a = Less
  | c, Nil, a, b, rest, Both ca r => ca
  | c, Cons (e, f) ys2, a, b, rest, Both ce r => ord.trans c e a ce (Map.Spec.belowLater e ys2 a b rest r)

-- Inserting a key above every key of a list puts it at the end.
theorem Map.Spec.insertLast [auto ord: Ord k]: (lo: Option k) -> (ys: List (k, v)) -> (a: k) -> (b: v) -> (rest: List (k, v)) ->
    Map.Spec.Ascending ord lo (List.append ys (Cons (a, b) rest)) ->
    Map.Spec.insert a b ys = List.append ys (Cons (a, b) Nil)
  | lo, Nil, a, b, rest, asc => rfl
  | lo, Cons (c, d) ys2, a, b, rest, Both lc r =>
    Eq.trans (Map.Spec.insertWithGreater (new old => new) a b c d ys2
        (Eq.trans (ord.flip c a) (Eq.cong Ordering.flip (Map.Spec.belowLater c ys2 a b rest r))))
      (Eq.cong (zs => Cons (c, d) zs) (Map.Spec.insertLast (Some c) ys2 a b rest r))

-- Leaving an entry out of a sorted list keeps it sorted.
theorem Map.Spec.ascendingDrop [auto ord: Ord k]: (lo: Option k) -> (ys: List (k, v)) -> (a: k) -> (b: v) -> (zs: List (k, v)) ->
    Map.Spec.Ascending ord lo (List.append ys (Cons (a, b) zs)) -> Map.Spec.Ascending ord lo (List.append ys zs)
  | lo, Nil, a, b, Nil, asc => Trivial
  | lo, Nil, a, b, Cons (c, d) zs2, Both la (Both ac r) => Both (Map.Tree.aboveTrans ord lo a c la ac) r
  | lo, Cons (c, d) ys2, a, b, zs, Both lc r => Both lc (Map.Spec.ascendingDrop (Some c) ys2 a b zs r)

theorem Map.Spec.filterOnto [auto ord: Ord k] (p: k -> v -> Bool): (ys: List (k, v)) -> (xs: List (k, v)) ->
    Map.Spec.Ascending ord None (List.append ys xs) ->
    Map.Spec.foldLeft (l key value => if p key value then Map.Spec.insert key value l else l) ys xs
      = List.append ys (List.filter (e => p e.fst e.snd) xs)
  | ys, Nil, asc => Eq.sym (List.appendNil ys)
  | ys, Cons (a, b) rest, asc =>
    match c: p a b with
      | True =>
        rewrite Map.Spec.insertLast None ys a b rest asc in
        Eq.trans
          (Map.Spec.filterOnto p (List.append ys (Cons (a, b) Nil)) rest
            (rewrite List.appendAssoc ys (Cons (a, b) Nil) rest in asc))
          (List.appendAssoc ys (Cons (a, b) Nil) (List.filter (e => p e.fst e.snd) rest))
      | False => Map.Spec.filterOnto p ys rest (Map.Spec.ascendingDrop None ys a b rest asc)

theorem Map.toListFilterList [auto ord: Ord k] (p: k -> v -> Bool) (m: Map k v):
    Map.toList (Map.filter p m) = List.filter (e => p e.fst e.snd) (Map.toList m) :=
  Eq.trans (Map.toListFilter p m) (Map.Spec.filterOnto p Nil (Map.toList m) (Map.toListSorted m))

-- Equivalent maps: the same entries, whatever their trees' shapes

def Map.Equiv (m: Map k v [ord := o]) (n: Map k v [ord := o]): Prop := Map.toList m = Map.toList n

theorem Map.equivRefl (m: Map k v [ord := o]): Map.Equiv m m := rfl

theorem Map.equivSym (m: Map k v [ord := o]) (n: Map k v [ord := o]) (h: Map.Equiv m n): Map.Equiv n m := Eq.sym h

theorem Map.equivTrans (m: Map k v [ord := o]) (n: Map k v [ord := o]) (p: Map k v [ord := o])
    (h1: Map.Equiv m n) (h2: Map.Equiv n p): Map.Equiv m p :=
  Eq.trans h1 h2

-- The same `get` for every key means the same entries; with
-- `Map.getRespects`, `Map.Equiv` is exactly "the same `get` everywhere".
theorem Map.equivOfGet [auto ord: Ord k] (m: Map k v) (n: Map k v) (h: (key: k) -> Map.get key m = Map.get key n):
    Map.Equiv m n :=
  Map.Spec.extLookup None (Map.toList m) (Map.toList n) (Map.toListSorted m) (Map.toListSorted n)
    (key => Eq.trans (Eq.sym (Map.getToList key m)) (Eq.trans (h key) (Map.getToList key n)))

-- Each operation respects `Map.Equiv`: equivalent maps give equal results,
-- or equivalent maps.

theorem Map.getRespects [auto ord: Ord k] (key: k) (m: Map k v) (n: Map k v) (h: Map.Equiv m n):
    Map.get key m = Map.get key n :=
  Eq.trans (Map.getToList key m) (Eq.trans (Eq.cong (Map.Tree.lookupList key) h) (Eq.sym (Map.getToList key n)))

theorem Map.getOrRespects [auto ord: Ord k] (d: v) (key: k) (m: Map k v) (n: Map k v) (h: Map.Equiv m n):
    Map.getOr d key m = Map.getOr d key n :=
  Eq.cong (Option.getOrElse d) (Map.getRespects key m n h)

theorem Map.containsRespects [auto ord: Ord k] (key: k) (m: Map k v) (n: Map k v) (h: Map.Equiv m n):
    Map.contains key m = Map.contains key n :=
  rewrite Map.getRespects key m n h in rfl

theorem Map.sizeRespects (m: Map k v [ord := o]) (n: Map k v [ord := o]) (h: Map.Equiv m n): Map.size m = Map.size n :=
  Eq.trans (Map.sizeToList m) (Eq.trans (Eq.cong List.length h) (Eq.sym (Map.sizeToList n)))

theorem Map.isEmptyRespects (m: Map k v [ord := o]) (n: Map k v [ord := o]) (h: Map.Equiv m n): Map.isEmpty m = Map.isEmpty n :=
  Eq.cong (s => Nat.equal s 0) (Map.sizeRespects m n h)

theorem Map.keysRespects (m: Map k v [ord := o]) (n: Map k v [ord := o]) (h: Map.Equiv m n): Map.keys m = Map.keys n :=
  Eq.cong (List.map Pair.fst) h

theorem Map.valuesRespects (m: Map k v [ord := o]) (n: Map k v [ord := o]) (h: Map.Equiv m n): Map.values m = Map.values n :=
  Eq.cong (List.map Pair.snd) h

theorem Map.foldLeftRespects (f: b -> k -> v -> b) (z: b) (m: Map k v [ord := o]) (n: Map k v [ord := o]) (h: Map.Equiv m n):
    Map.foldLeft f z m = Map.foldLeft f z n :=
  Eq.trans (Map.foldLeftToList f z m) (Eq.trans (Eq.cong (Map.Spec.foldLeft f z) h) (Eq.sym (Map.foldLeftToList f z n)))

theorem Map.insertWithRespects [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (m: Map k v) (n: Map k v) (h: Map.Equiv m n):
    Map.Equiv (Map.insertWith f key value m) (Map.insertWith f key value n) :=
  Eq.trans (Map.toListInsertWith f key value m)
    (Eq.trans (Eq.cong (Map.Spec.insertWith f key value) h) (Eq.sym (Map.toListInsertWith f key value n)))

theorem Map.insertRespects [auto ord: Ord k] (key: k) (value: v) (m: Map k v) (n: Map k v) (h: Map.Equiv m n):
    Map.Equiv (Map.insert key value m) (Map.insert key value n) :=
  Map.insertWithRespects (new old => new) key value m n h

theorem Map.removeRespects [auto ord: Ord k] (key: k) (m: Map k v) (n: Map k v) (h: Map.Equiv m n):
    Map.Equiv (Map.remove key m) (Map.remove key n) :=
  Eq.trans (Map.toListRemove key m) (Eq.trans (Eq.cong (Map.Spec.remove key) h) (Eq.sym (Map.toListRemove key n)))

theorem Map.alterRespects [auto ord: Ord k] (f: Option v -> Option v) (key: k) (m: Map k v) (n: Map k v) (h: Map.Equiv m n):
    Map.Equiv (Map.alter f key m) (Map.alter f key n) :=
  Eq.trans (Map.toListAlter f key m) (Eq.trans (Eq.cong (Map.Spec.alter f key) h) (Eq.sym (Map.toListAlter f key n)))

theorem Map.adjustRespects [auto ord: Ord k] (f: v -> v) (key: k) (m: Map k v) (n: Map k v) (h: Map.Equiv m n):
    Map.Equiv (Map.adjust f key m) (Map.adjust f key n) :=
  Eq.trans (Map.toListAdjust f key m) (Eq.trans (Eq.cong (Map.Spec.adjust f key) h) (Eq.sym (Map.toListAdjust f key n)))

theorem Map.mapRespects (f: v -> w) (m: Map k v [ord := o]) (n: Map k v [ord := o]) (h: Map.Equiv m n):
    Map.Equiv (Map.map f m) (Map.map f n) :=
  Eq.trans (Map.toListMap f m) (Eq.trans (Eq.cong (Map.Spec.mapValues f) h) (Eq.sym (Map.toListMap f n)))

theorem Map.filterRespects [auto ord: Ord k] (p: k -> v -> Bool) (m: Map k v) (n: Map k v) (h: Map.Equiv m n):
    Map.Equiv (Map.filter p m) (Map.filter p n) :=
  Eq.trans (Map.toListFilter p m) (Eq.trans (Eq.cong (Map.Spec.filter p) h) (Eq.sym (Map.toListFilter p n)))

theorem Map.unionRespects [auto ord: Ord k] (a: Map k v) (a2: Map k v) (b: Map k v) (b2: Map k v)
    (ha: Map.Equiv a a2) (hb: Map.Equiv b b2): Map.Equiv (Map.union a b) (Map.union a2 b2) :=
  Eq.trans (Map.toListUnion a b)
    (Eq.trans (Eq.cong (l => Map.Spec.union l (Map.toList b)) ha)
      (Eq.trans (Eq.cong (l => Map.Spec.union (Map.toList a2) l) hb) (Eq.sym (Map.toListUnion a2 b2))))

-- Folds whose steps agree give the same result; so `filter` with
-- predicates that agree keeps the same entries.
theorem Map.Spec.foldLeftCongr (f: b -> k -> v -> b) (g: b -> k -> v -> b)
    (h: (z: b) -> (key: k) -> (value: v) -> f z key value = g z key value):
    (z: b) -> (xs: List (k, v)) -> Map.Spec.foldLeft f z xs = Map.Spec.foldLeft g z xs
  | z, Nil => rfl
  | z, Cons (kk, vv) rest =>
    Eq.trans (Map.Spec.foldLeftCongr f g h (f z kk vv) rest) (Eq.cong (y => Map.Spec.foldLeft g y rest) (h z kk vv))

theorem Map.filterCongr [auto ord: Ord k] (p: k -> v -> Bool) (q: k -> v -> Bool)
    (same: (key: k) -> (value: v) -> p key value = q key value) (m: Map k v):
    Map.Equiv (Map.filter p m) (Map.filter q m) :=
  Eq.trans (Map.toListFilter p m)
    (Eq.trans (Map.Spec.foldLeftCongr
        ((l: List (k, v)) (key: k) (value: v) => if p key value then Map.Spec.insert key value l else l)
        ((l: List (k, v)) (key: k) (value: v) => if q key value then Map.Spec.insert key value l else l)
        (l key value => rewrite same key value in rfl) Nil (Map.toList m))
      (Eq.sym (Map.toListFilter q m)))

-- Deciding `Map.Equiv` by comparing the entry lists. It needs `DecEq` for
-- the values (the keys have one in their `Ord`): a test that said "same"
-- exactly when the entries are equal would decide equality of any two
-- values, through one-entry maps.
def Map.same [auto dv: DecEq v] (m: Map k v [ord := o]) (n: Map k v [ord := o]): Bool :=
  Map.toList m == Map.toList n

theorem Map.sameSound [auto dv: DecEq v] (m: Map k v [ord := o]) (n: Map k v [ord := o])
    (h: Map.same m n = True): Map.Equiv m n :=
  Decidable.toBoolSound (DecEq.decide (Map.toList m) (Map.toList n)) h

theorem Map.sameComplete [auto dv: DecEq v] (m: Map k v [ord := o]) (n: Map k v [ord := o])
    (h: Map.Equiv m n): Map.same m n = True :=
  Decidable.toBoolOf (DecEq.decide (Map.toList m) (Map.toList n)) h

theorem Map.sameIff [auto dv: DecEq v] (m: Map k v [ord := o]) (n: Map k v [ord := o]):
    Iff (Map.same m n = True) (Map.Equiv m n) :=
  { forward = Map.sameSound m n, backward = Map.sameComplete m n }

def Map.Spec.example: List (Nat, Text) := [(1, "a"), (3, "c")]

test "map spec: insert" :=
  Map.Spec.insert 2 "b" Map.Spec.example == [(1, "a"), (2, "b"), (3, "c")]
    && Map.Spec.insert 3 "C" Map.Spec.example == [(1, "a"), (3, "C")]
    && Map.Spec.insert 4 "d" Map.Spec.example == [(1, "a"), (3, "c"), (4, "d")]
test "map spec: remove" :=
  Map.Spec.remove 1 Map.Spec.example == [(3, "c")] && Map.Spec.remove 2 Map.Spec.example == Map.Spec.example
test "map spec: fromList, later wins" := Map.Spec.fromList [(2, "x"), (1, "a"), (2, "b")] == [(1, "a"), (2, "b")]
test "map: same in any order" :=
  Map.same (Map.fromList [(1, "a"), (2, "b"), (3, "c")]: Map Nat Text) (Map.fromList [(3, "c"), (1, "a"), (2, "b")])
test "map: same sees a changed value" :=
  !(Map.same (Map.fromList [(1, "a"), (2, "b")]: Map Nat Text) (Map.fromList [(1, "a"), (2, "B")]))
