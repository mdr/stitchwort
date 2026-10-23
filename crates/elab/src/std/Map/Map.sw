-- `Map k v`: finite maps from keys to values, with the ordering of the keys
-- in the map's type (docs/proposals/interfaces.md §7.5, D169): `Map Text Nat`
-- is `Map Text Nat [ord := Text.instOrd]`, and a map built with another
-- ordering has another type. A map is a quotient (docs/proposals/
-- map-equality.md §8): its representative is a `Map.Raw`, a weight-balanced
-- search tree (std/Map/Raw.sw), and two representatives with the same
-- entries in key order are the same map. So `m = n` exactly when `m` and `n`
-- have the same entries (`Map.eqIffToListEq`), for any type of values, and
-- `==` compares the entries. Each operation is the raw one, lifted with the
-- lemma that it respects `Map.Raw.Equiv` (std/Map/Spec.sw). At run time a
-- map is its tree, in one record.
-- Insertion, lookup and removal take O(log n) comparisons; `size` is O(1).
-- docs/proposals/map-set.md.

import Std (Eq)

-- A record around the quotient, so that dot notation on a map finds `Map`'s
-- functions (`m.insert 3 "c"`).
type Map (k: Type) (v: Type) [auto ord: Ord k] = { raw: Quot (Map.Raw k v [ord := ord]) Map.Raw.Equiv }

-- The map whose entries are the raw map's.
def Map.ofRaw (rawMap: Map.Raw k v [ord := o]): Map k v [ord := o] := { raw = Quot.mk rawMap }

-- To prove something of every map, prove it of the map of every raw map.
theorem Map.indRaw [p: Map k v [ord := o] -> Prop] (h: (r: Map.Raw k v [ord := o]) -> p (Map.ofRaw r)):
    (m: Map k v [ord := o]) -> p m
  | { raw = q } => Quot.ind [p := q' => p { raw = q' }] h q

-- Building

-- No entries.
def Map.empty [auto ord: Ord k]: Map k v := Map.ofRaw Map.Raw.empty

-- One entry.
def Map.singleton [auto ord: Ord k] (key: k) (value: v): Map k v := Map.ofRaw (Map.Raw.singleton key value)

-- A map of the pairs; a later pair's value replaces an earlier one's.
def Map.fromList [auto ord: Ord k] (xs: List (k, v)): Map k v := Map.ofRaw (Map.Raw.fromList xs)

-- Reading

-- The entries, in key order.
def Map.toList (m: Map k v [ord := o]): List (k, v) := Quot.lift Map.Raw.toList (a b same => same) m.raw

-- The value at `key`, if there is one.
def Map.get [auto ord: Ord k] (key: k) (m: Map k v): Option v :=
  Quot.lift (Map.Raw.get key) (a b same => Map.Raw.getRespects key a b same) m.raw

-- The value at `key`, or `fallback`.
def Map.getOr [auto ord: Ord k] (fallback: v) (key: k) (m: Map k v): v := Option.getOrElse fallback (Map.get key m)

def Map.contains [auto ord: Ord k] (key: k) (m: Map k v): Bool := match Map.get key m with
  | Some _ => True
  | None => False

-- The number of entries, O(1).
def Map.size (m: Map k v [ord := o]): Nat := Quot.lift Map.Raw.size (a b same => Map.Raw.sizeRespects a b same) m.raw

def Map.isEmpty (m: Map k v [ord := o]): Bool := Nat.equal (Map.size m) 0

def Map.keys (m: Map k v [ord := o]): List k := List.map Pair.fst (Map.toList m)

def Map.values (m: Map k v [ord := o]): List v := List.map Pair.snd (Map.toList m)

-- Left fold over the entries in key order: `f (f initial k1 v1) k2 v2`.
def Map.foldLeft (f: b -> k -> v -> b) (initial: b) (m: Map k v [ord := o]): b :=
  Quot.lift (Map.Raw.foldLeft f initial) (a b same => Map.Raw.foldLeftRespects f initial a b same) m.raw

-- Changing

-- `value` at `key`; if `key` has a value already, `f value old` (so
-- `Map.insertWith Nat.add key 1 counts` counts).
def Map.insertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (m: Map k v): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.insertWith f key value rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.insertWithRespects f key value a b same))
    m.raw
}

-- `value` at `key`, replacing any value there.
def Map.insert [auto ord: Ord k] (key: k) (value: v) (m: Map k v): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.insert key value rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.insertRespects key value a b same))
    m.raw
}

-- Without `key` (the same map if it isn't there).
def Map.remove [auto ord: Ord k] (key: k) (m: Map k v): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.remove key rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.removeRespects key a b same))
    m.raw
}

-- The value at `key` changed by `f`, which sees `None` when there's none
-- and removes the entry by returning `None`.
def Map.alter [auto ord: Ord k] (f: Option v -> Option v) (key: k) (m: Map k v): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.alter f key rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.alterRespects f key a b same))
    m.raw
}

-- The value at `key` changed by `f`, if there is one.
def Map.adjust [auto ord: Ord k] (f: v -> v) (key: k) (m: Map k v): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.adjust f key rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.adjustRespects f key a b same))
    m.raw
}

-- Every value changed by `f`; the keys stay.
def Map.map (f: v -> w) (m: Map k v [ord := o]): Map k w [ord := o] := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.map f rawMap): Quot (Map.Raw k w [ord := o]) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.mapRespects f a b same))
    m.raw
}

-- The entries for which `p` holds.
def Map.filter [auto ord: Ord k] (p: k -> v -> Bool) (m: Map k v): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.filter p rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.filterRespects p a b same))
    m.raw
}

-- `Map.union` with its first argument a raw map.
def Map.unionRaw [auto ord: Ord k] (a: Map.Raw k v) (q: Quot (Map.Raw k v) Map.Raw.Equiv): Quot (Map.Raw k v) Map.Raw.Equiv :=
  Quot.lift
    (b => (Quot.mk (Map.Raw.union a b): Quot (Map.Raw k v) Map.Raw.Equiv))
    (b b2 same => Quot.sound (Map.Raw.unionRespects a a b b2 rfl same))
    q

-- Both maps' entries; where both have a key, the first map's value.
def Map.union [auto ord: Ord k] (a: Map k v) (b: Map k v): Map k v := {
  raw = Quot.lift
    (rawMap => Map.unionRaw rawMap b.raw)
    (a1 a2 same =>
      Quot.ind
        [p := q => Map.unionRaw a1 q = Map.unionRaw a2 q]
        (rawMap => Quot.sound (Map.Raw.unionRespects a1 a2 rawMap rawMap same rfl))
        b.raw)
    a.raw
}

-- More building

-- A map of the pairs; where a key comes again, `f new old` combines its
-- values, in list order (`Map.fromListWith Nat.add` sums them).
def Map.fromListWith [auto ord: Ord k] (f: v -> v -> v) (xs: List (k, v)): Map k v :=
  List.foldLeft (m entry => Map.insertWith f entry.fst entry.snd m) Map.empty xs

-- The elements under their keys, each list in list order:
-- `Map.groupBy (n => n % 2) [1, 2, 3]` is `Map.fromList [(0, [2]), (1, [1, 3])]`.
def Map.groupBy [auto ord: Ord k] (key: a -> k) (xs: List a): Map k (List a) :=
  List.foldRight (x m => Map.insertWith List.append (key x) [x] m) Map.empty xs

-- Each element under its key; where elements share a key, the FIRST one is
-- kept: `Map.indexBy Text.length ["ab", "c", "de"]` is
-- `Map.fromList [(1, "c"), (2, "ab")]`. `foldRight` meets the last element
-- first, so the newer value, from the earlier element, wins.
def Map.indexBy [auto ord: Ord k] (key: a -> k) (xs: List a): Map k a :=
  List.foldRight (element index => Map.insertWith (newer older => newer) (key element) element index) Map.empty xs

-- How many times each element occurs.
def Map.counts [auto ord: Ord k] (xs: List k): Map k Nat := List.foldLeft (m x => Map.insertWith Nat.add x 1 m) Map.empty xs

-- More looking up

-- The first entry, in key order, for which `p` holds.
def Map.find (p: k -> v -> Bool) (m: Map k v [ord := o]): Option (k, v) := List.find (e => p e.fst e.snd) (Map.toList m)

-- The entry with the smallest key, O(log n).
def Map.min (m: Map k v [ord := o]): Option (k, v) := Quot.lift Map.Raw.min (a b same => Map.Raw.minRespects a b same) m.raw

-- The entry with the largest key, O(log n).
def Map.max (m: Map k v [ord := o]): Option (k, v) := Quot.lift Map.Raw.max (a b same => Map.Raw.maxRespects a b same) m.raw

-- The entry with the largest key below `key` (strictly), O(log n).
def Map.below [auto ord: Ord k] (key: k) (m: Map k v): Option (k, v) :=
  Quot.lift (Map.Raw.below key) (a b same => Map.Raw.belowRespects key a b same) m.raw

-- The entry with the smallest key above `key` (strictly), O(log n).
def Map.above [auto ord: Ord k] (key: k) (m: Map k v): Option (k, v) :=
  Quot.lift (Map.Raw.above key) (a b same => Map.Raw.aboveRespects key a b same) m.raw

-- More combining

-- Both maps' entries; where both have a key, `f` of the first map's value
-- and the second's.
def Map.unionWith [auto ord: Ord k] (f: v -> v -> v) (a: Map k v) (b: Map k v): Map k v :=
  Map.foldLeft (acc key value => Map.insertWith f key value acc) b a

-- The keys of both maps, with `f` of their values.
def Map.intersectWith [auto ord: Ord k] (f: v -> w -> x) (a: Map k v) (b: Map k w): Map k x :=
  Map.filterMap (key value => Option.map (f value) (Map.get key b)) a

-- The entries of `a` whose keys aren't in `b`.
def Map.difference [auto ord: Ord k] (a: Map k v) (b: Map k w): Map k v := Map.filter (key value => !(Map.contains key b)) a

-- More transforming

-- Every value changed by `f`, which also sees its key; the keys stay.
def Map.mapWithKey (f: k -> v -> w) (m: Map k v [ord := o]): Map k w [ord := o] := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.mapWithKey f rawMap): Quot (Map.Raw k w [ord := o]) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.mapWithKeyRespects f a b same))
    m.raw
}

-- `Map.filterMap`'s step: the entry `f` makes, if it makes one.
def Map.filterMapStep [auto ord: Ord k] (f: k -> v -> Option w) (acc: Map k w) (key: k) (value: v): Map k w := match f key value with
  | Some y => Map.insert key y acc
  | None => acc

-- The values `f` keeps, changed; `f` sees each key and value.
def Map.filterMap [auto ord: Ord k] (f: k -> v -> Option w) (m: Map k v): Map k w := Map.foldLeft (Map.filterMapStep f) Map.empty m

-- The entries for which `p` holds, and those for which it doesn't.
def Map.partition [auto ord: Ord k] (p: k -> v -> Bool) (m: Map k v): (Map k v, Map k v) :=
  (Map.filter p m, Map.filter (key value => !(p key value)) m)

-- Every key changed by `f`, into a map ordered by `j`'s ordering; where two
-- keys go to one, the later (larger) key's value wins.
def Map.mapKeys [auto ord: Ord j] (f: k -> j) (m: Map k v [ord := o]): Map j v :=
  Map.fromList (List.map (e => (f e.fst, e.snd)) (Map.toList m))

-- More reading

-- Right fold over the entries in key order: `f k1 v1 (f k2 v2 initial)`.
def Map.foldRight (f: k -> v -> b -> b) (initial: b) (m: Map k v [ord := o]): b := List.foldRight (e acc => f e.fst e.snd acc) initial (Map.toList m)

-- Whether some entry satisfies `p`.
def Map.any (p: k -> v -> Bool) (m: Map k v [ord := o]): Bool := List.any (e => p e.fst e.snd) (Map.toList m)

-- Whether every entry satisfies `p`.
def Map.all (p: k -> v -> Bool) (m: Map k v [ord := o]): Bool := List.all (e => p e.fst e.snd) (Map.toList m)

-- The number of entries satisfying `p`.
def Map.count (p: k -> v -> Bool) (m: Map k v [ord := o]): Nat := List.count (e => p e.fst e.snd) (Map.toList m)

-- The entries with `lo <= key < hi`.
def Map.range [auto ord: Ord k] (lo: k) (hi: k) (m: Map k v): Map k v :=
  Map.filter (key value => !(Map.Spec.isLess key lo) && Map.Spec.isLess key hi) m

-- Equality: the same entries

-- Two classes with the same entries are the same class.
theorem Map.rawInjective (p: Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv) (q: Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv):
    Map.toList { raw = p } = Map.toList { raw = q } -> p = q :=
  let motive: Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv -> Prop :=
    p' => (q': Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv) -> Map.toList { raw = p' } = Map.toList { raw = q' } -> p' = q'
  let fromMk: (a: Map.Raw k v [ord := o]) -> motive (Quot.mk a) :=
    a q' =>
      Quot.ind
        [p := q'' => Map.toList { raw = Quot.mk a } = Map.toList { raw = q'' } -> Quot.mk a = q'']
        (b same => Quot.sound same)
        q'
  Quot.ind [p := motive] fromMk p q

-- Maps with the same entries are equal, whatever their values' type.
theorem Map.toListInjective: (m: Map k v [ord := o]) -> (n: Map k v [ord := o]) -> Map.toList m = Map.toList n -> m = n
  | { raw = p }, { raw = q }, same => Eq.cong (r => ({ raw = r }: Map k v [ord := o])) (Map.rawInjective p q same)

-- Equal maps have the same entries, and maps with the same entries are equal.
theorem Map.eqIffToListEq (m: Map k v [ord := o]) (n: Map k v [ord := o]): Iff (m = n) (Map.toList m = Map.toList n) := {
  forward = same => Eq.cong Map.toList same,
  backward = Map.toListInjective m n
}

-- The entries are in strictly increasing key order, and `get` looks a key up
-- in them.
theorem Map.toListSorted (m: Map k v [ord := o]): Map.Spec.Sorted o (Map.toList m) :=
  Map.indRaw [p := m' => Map.Spec.Sorted o (Map.toList m')] (r => Map.Raw.toListSorted r) m

theorem Map.getToList [auto ord: Ord k] (key: k) (m: Map k v): Map.get key m = Map.Tree.lookupList key (Map.toList m) :=
  Map.indRaw [p := m' => Map.get key m' = Map.Tree.lookupList key (Map.toList m')] (r => Map.Raw.getToList key r) m

-- An entry is in `toList` exactly when `get` finds it.
theorem Map.memToList [auto ord: Ord k] (key: k) (value: v) (m: Map k v): Iff (List.Mem (key, value) (Map.toList m)) (Map.get key m = Some value) := {
  forward = mem => Eq.trans (Map.getToList key m) (Map.Spec.lookupOfMem key value None (Map.toList m) (Map.toListSorted m) mem),
  backward = found => Map.Spec.memOfLookup key value (Map.toList m) (Eq.trans (Eq.sym (Map.getToList key m)) found)
}

-- Maps that agree on every key are equal, whatever their values' type.
theorem Map.ext (m: Map k v [ord := o]) (n: Map k v [ord := o]) (h: (key: k) -> Map.get key m = Map.get key n): m = n :=
  Map.toListInjective m n
    (Map.Spec.extLookup None (Map.toList m) (Map.toList n) (Map.toListSorted m) (Map.toListSorted n)
      (key => Eq.trans (Eq.sym (Map.getToList key m)) (Eq.trans (h key) (Map.getToList key n))))

-- `==`: compare the entry lists, the keys by the map's ordering. The branch
-- is chosen by the list comparison; `Quot.sound` is only inside the `Yes`
-- proof, so `==` computes.
def Map.decEq [auto dv: DecEq v] (m: Map k v [ord := o]) (n: Map k v [ord := o]): Decidable (m = n) :=
  match List.decEq (Pair.decEq o.eq.decide dv.decide) (Map.toList m) (Map.toList n) with
    | Yes same => Yes (Map.toListInjective m n same)
    | No differ => No (same => differ (Eq.cong Map.toList same))

instance Map.instDecEq [auto dv: DecEq v]: DecEq (Map k v [ord := o]) := { decide = Map.decEq }

-- `compare`: the entry lists, lexicographically, the keys by the map's
-- ordering. Each law comes from the list order's, `equal` through
-- `toListInjective`.
def Map.compare [auto vord: Ord v] (m: Map k v [ord := o]) (n: Map k v [ord := o]): Ordering :=
  List.compareLex (Pair.compareWith o.compare vord.compare) (Map.toList m) (Map.toList n)

instance Map.instOrd [auto vord: Ord v]: Ord (Map k v [ord := o]) :=
  Ord.fromCompare [decEq := Map.instDecEq [dv := vord.eq]] Map.compare
    (m n same =>
      Map.toListInjective m n
        (List.compareLexEqual (Pair.compareWith o.compare vord.compare)
          (Pair.compareWithEqual o.compare vord.compare o.equal vord.equal) (Map.toList m) (Map.toList n) same))
    (m n =>
      List.compareLexFlip (Pair.compareWith o.compare vord.compare)
        (Pair.compareWithFlip o.compare vord.compare o.flip vord.flip) (Map.toList m) (Map.toList n))
    (m n p =>
      List.compareLexTrans (Pair.compareWith o.compare vord.compare)
        (Pair.compareWithEqual o.compare vord.compare o.equal vord.equal)
        (Pair.compareWithTrans o.compare vord.compare o.equal o.trans vord.trans)
        (Map.toList m) (Map.toList n) (Map.toList p))

-- `Map.fromList [(1, "a"), (2, "b")]`, in key order, whatever the ordering.
instance Map.instShow [auto showK: Show k] [auto showV: Show v]: Show (Map k v [ord := o]) :=
  Show.fromText (m => Text.append "Map.fromList "
    (Show.list (p => Pair.showWith (x => Show.toSource x) (y => Show.toSource y) p) (Map.toList m)))

-- What each operation does to the entries (the raw maps' lemmas, for every
-- map)

theorem Map.toListEmpty [auto ord: Ord k]: Map.toList (Map.empty: Map k v) = Nil := rfl

theorem Map.toListSingleton [auto ord: Ord k] (key: k) (value: v): Map.toList (Map.singleton key value: Map k v) = [(key, value)] := rfl

theorem Map.toListFromList [auto ord: Ord k] (xs: List (k, v)): Map.toList (Map.fromList xs: Map k v) = Map.Spec.fromList xs :=
  Map.Raw.toListFromList xs

theorem Map.toListInsertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (m: Map k v):
    Map.toList (Map.insertWith f key value m) = Map.Spec.insertWith f key value (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.insertWith f key value m') = Map.Spec.insertWith f key value (Map.toList m')]
    (r => Map.Raw.toListInsertWith f key value r) m

theorem Map.toListInsert [auto ord: Ord k] (key: k) (value: v) (m: Map k v):
    Map.toList (Map.insert key value m) = Map.Spec.insert key value (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.insert key value m') = Map.Spec.insert key value (Map.toList m')]
    (r => Map.Raw.toListInsert key value r) m

theorem Map.toListRemove [auto ord: Ord k] (key: k) (m: Map k v): Map.toList (Map.remove key m) = Map.Spec.remove key (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.remove key m') = Map.Spec.remove key (Map.toList m')] (r => Map.Raw.toListRemove key r) m

theorem Map.toListAlter [auto ord: Ord k] (f: Option v -> Option v) (key: k) (m: Map k v):
    Map.toList (Map.alter f key m) = Map.Spec.alter f key (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.alter f key m') = Map.Spec.alter f key (Map.toList m')] (r => Map.Raw.toListAlter f key r) m

theorem Map.toListAdjust [auto ord: Ord k] (f: v -> v) (key: k) (m: Map k v):
    Map.toList (Map.adjust f key m) = Map.Spec.adjust f key (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.adjust f key m') = Map.Spec.adjust f key (Map.toList m')] (r => Map.Raw.toListAdjust f key r) m

theorem Map.toListMap (f: v -> w) (m: Map k v [ord := o]): Map.toList (Map.map f m) = Map.Spec.mapValues f (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.map f m') = Map.Spec.mapValues f (Map.toList m')] (r => Map.Raw.toListMap f r) m

theorem Map.toListFilter [auto ord: Ord k] (p: k -> v -> Bool) (m: Map k v): Map.toList (Map.filter p m) = Map.Spec.filter p (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.filter p m') = Map.Spec.filter p (Map.toList m')] (r => Map.Raw.toListFilter p r) m

-- `filter` keeps the entries for which the test holds, in key order.
theorem Map.toListFilterList [auto ord: Ord k] (p: k -> v -> Bool) (m: Map k v):
    Map.toList (Map.filter p m) = List.filter (e => p e.fst e.snd) (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.filter p m') = List.filter (e => p e.fst e.snd) (Map.toList m')]
    (r => Map.Raw.toListFilterList p r) m

theorem Map.toListUnion [auto ord: Ord k] (a: Map k v) (b: Map k v):
    Map.toList (Map.union a b) = Map.Spec.union (Map.toList a) (Map.toList b) :=
  Map.indRaw [p := a' => Map.toList (Map.union a' b) = Map.Spec.union (Map.toList a') (Map.toList b)]
    (ra =>
      Map.indRaw [p := b' => Map.toList (Map.union (Map.ofRaw ra) b') = Map.Spec.union (Map.toList (Map.ofRaw ra)) (Map.toList b')]
        (rb => Map.Raw.toListUnion ra rb) b)
    a

theorem Map.foldLeftToList (f: b -> k -> v -> b) (z: b) (m: Map k v [ord := o]):
    Map.foldLeft f z m = Map.Spec.foldLeft f z (Map.toList m) :=
  Map.indRaw [p := m' => Map.foldLeft f z m' = Map.Spec.foldLeft f z (Map.toList m')] (r => Map.Raw.foldLeftToList f z r) m

theorem Map.sizeToList (m: Map k v [ord := o]): Map.size m = List.length (Map.toList m) :=
  Map.indRaw [p := m' => Map.size m' = List.length (Map.toList m')] (r => Map.Raw.sizeToList r) m

-- Inserting adds an entry unless the key is there already.
theorem Map.sizeInsert [auto ord: Ord k] (key: k) (value: v) (m: Map k v):
    Map.size (Map.insert key value m) = (if Map.contains key m then Map.size m else Map.size m + 1) :=
  rewrite Map.sizeToList (Map.insert key value m), Map.toListInsert key value m, Map.sizeToList m in
  match c: Map.get key m with
    | Some found =>
      Map.Spec.lengthInsertPresent key value found None (Map.toList m) (Map.toListSorted m) (Eq.trans (Eq.sym (Map.getToList key m)) c)
    | None =>
      Eq.trans (Map.Spec.lengthInsertAbsent key value (Map.toList m) (Eq.trans (Eq.sym (Map.getToList key m)) c))
        (Eq.sym (Nat.addOne (List.length (Map.toList m))))

-- Removing takes an entry away if the key is there.
theorem Map.sizeRemove [auto ord: Ord k] (key: k) (m: Map k v):
    Map.size (Map.remove key m) = (if Map.contains key m then Map.size m - 1 else Map.size m) :=
  rewrite Map.sizeToList (Map.remove key m), Map.toListRemove key m, Map.sizeToList m in
  match c: Map.get key m with
    | Some found =>
      Eq.cong (n => n - 1)
        (Map.Spec.lengthRemovePresent key found None (Map.toList m) (Map.toListSorted m) (Eq.trans (Eq.sym (Map.getToList key m)) c))
    | None => Eq.cong List.length (Map.Spec.removeAbsent key (Map.toList m) (Eq.trans (Eq.sym (Map.getToList key m)) c))

theorem Map.toListMapWithKey (f: k -> v -> w) (m: Map k v [ord := o]): Map.toList (Map.mapWithKey f m) = Map.Spec.mapWithKey f (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.mapWithKey f m') = Map.Spec.mapWithKey f (Map.toList m')] (r => Map.Raw.toListMapWithKey f r) m

theorem Map.minToList (m: Map k v [ord := o]): Map.min m = List.head (Map.toList m) :=
  Map.indRaw [p := m' => Map.min m' = List.head (Map.toList m')] (r => Map.Raw.minToList r) m

theorem Map.maxToList (m: Map k v [ord := o]): Map.max m = List.last (Map.toList m) :=
  Map.indRaw [p := m' => Map.max m' = List.last (Map.toList m')] (r => Map.Raw.maxToList r) m

theorem Map.belowToList [auto ord: Ord k] (key: k) (m: Map k v):
    Map.below key m = List.last (List.filter (e => Map.Spec.isLess e.fst key) (Map.toList m)) :=
  Map.indRaw [p := m' => Map.below key m' = List.last (List.filter (e => Map.Spec.isLess e.fst key) (Map.toList m'))] (r => Map.Raw.belowToList key r) m

theorem Map.aboveToList [auto ord: Ord k] (key: k) (m: Map k v):
    Map.above key m = List.find (e => Map.Spec.isLess key e.fst) (Map.toList m) :=
  Map.indRaw [p := m' => Map.above key m' = List.find (e => Map.Spec.isLess key e.fst) (Map.toList m')] (r => Map.Raw.aboveToList key r) m

-- What `get` says about each operation

theorem Map.getEmpty [auto ord: Ord k] (key: k): Map.get key (Map.empty: Map k v) = None := rfl

theorem Map.getInsert [auto ord: Ord k] (key: k) (value: v) (m: Map k v): (m |> Map.insert key value |> Map.get key) = Some value :=
  Map.indRaw [p := m' => (m' |> Map.insert key value |> Map.get key) = Some value] (r => Map.Raw.getInsert key value r) m

theorem Map.getInsertOther [auto ord: Ord k] (key: k) (value: v) (other: k) (ne: Not (other = key)) (m: Map k v):
    (m |> Map.insert key value |> Map.get other) = Map.get other m :=
  Map.indRaw [p := m' => (m' |> Map.insert key value |> Map.get other) = Map.get other m']
    (r => Map.Raw.getInsertOther key value other ne r) m

theorem Map.getInsertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (m: Map k v):
    Map.get key (Map.insertWith f key value m) = Some (Map.Tree.combine f value (Map.get key m)) :=
  Map.indRaw [p := m' => Map.get key (Map.insertWith f key value m') = Some (Map.Tree.combine f value (Map.get key m'))]
    (r => Map.Raw.getInsertWith f key value r) m

theorem Map.getMap [auto ord: Ord k] (f: v -> w) (key: k) (m: Map k v): Map.get key (Map.map f m) = Option.map f (Map.get key m) :=
  Map.indRaw [p := m' => Map.get key (Map.map f m') = Option.map f (Map.get key m')] (r => Map.Raw.getMap f key r) m

theorem Map.getFromList [auto ord: Ord k] (key: k) (xs: List (k, v)): Map.get key (Map.fromList xs) = Map.lookupLast key xs :=
  Map.Raw.getFromList key xs

theorem Map.getInsertWithOther [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (other: k) (ne: Not (other = key)) (m: Map k v):
    Map.get other (Map.insertWith f key value m) = Map.get other m :=
  Map.indRaw [p := m' => Map.get other (Map.insertWith f key value m') = Map.get other m'] (r => Map.Raw.getInsertWithOther f key value other ne r) m

theorem Map.getRemove [auto ord: Ord k] (key: k) (m: Map k v): Map.get key (Map.remove key m) = None :=
  Map.indRaw [p := m' => Map.get key (Map.remove key m') = None] (r => Map.Raw.getRemove key r) m

theorem Map.getRemoveOther [auto ord: Ord k] (key: k) (other: k) (ne: Not (other = key)) (m: Map k v):
    Map.get other (Map.remove key m) = Map.get other m :=
  Map.indRaw [p := m' => Map.get other (Map.remove key m') = Map.get other m'] (r => Map.Raw.getRemoveOther key other ne r) m

theorem Map.getAlter [auto ord: Ord k] (f: Option v -> Option v) (key: k) (m: Map k v): Map.get key (Map.alter f key m) = f (Map.get key m) :=
  Map.indRaw [p := m' => Map.get key (Map.alter f key m') = f (Map.get key m')] (r => Map.Raw.getAlter f key r) m

theorem Map.getAlterOther [auto ord: Ord k] (f: Option v -> Option v) (key: k) (other: k) (ne: Not (other = key)) (m: Map k v):
    Map.get other (Map.alter f key m) = Map.get other m :=
  Map.indRaw [p := m' => Map.get other (Map.alter f key m') = Map.get other m'] (r => Map.Raw.getAlterOther f key other ne r) m

theorem Map.getAdjust [auto ord: Ord k] (f: v -> v) (key: k) (m: Map k v): Map.get key (Map.adjust f key m) = Option.map f (Map.get key m) :=
  Map.indRaw [p := m' => Map.get key (Map.adjust f key m') = Option.map f (Map.get key m')] (r => Map.Raw.getAdjust f key r) m

theorem Map.getAdjustOther [auto ord: Ord k] (f: v -> v) (key: k) (other: k) (ne: Not (other = key)) (m: Map k v):
    Map.get other (Map.adjust f key m) = Map.get other m :=
  Map.indRaw [p := m' => Map.get other (Map.adjust f key m') = Map.get other m'] (r => Map.Raw.getAdjustOther f key other ne r) m

-- `filter` keeps the value at `key` if `p` holds of it.
theorem Map.getFilter [auto ord: Ord k] (p: k -> v -> Bool) (key: k) (m: Map k v):
    Map.get key (Map.filter p m) = Option.filter (p key) (Map.get key m) :=
  Eq.trans (Map.getToList key (Map.filter p m))
    (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.toListFilterList p m))
      (Eq.trans (Map.Spec.lookupFilter p key None (Map.toList m) (Map.toListSorted m))
        (Eq.cong (Option.filter (p key)) (Eq.sym (Map.getToList key m)))))

-- What a fold over sorted entries leaves at `key`, for a step that changes
-- only the key it's given (`atKey`, `elsewhere`): `unionWith`, `union` and
-- `filterMap` are such folds. A sorted list has at most one entry at `key`.
theorem Map.getFold [auto ord: Ord k] (step: Map k w -> k -> v -> Map k w) (h: v -> Option w -> Option w) (key: k)
    (atKey: (m: Map k w) -> (value: v) -> Map.get key (step m key value) = h value (Map.get key m))
    (elsewhere: (m: Map k w) -> (kk: k) -> (value: v) -> Not (key = kk) -> Map.get key (step m kk value) = Map.get key m):
    (lo: Option k) -> (xs: List (k, v)) -> (m: Map k w) -> Map.Spec.Ascending ord lo xs ->
    Map.get key (Map.Spec.foldLeft step m xs) = Map.Spec.atKey h (Map.Tree.lookupList key xs) (Map.get key m)
  | lo, Nil, m, asc => rfl
  | lo, Cons (kk, vv) rest, m, Both a arest =>
    rewrite Map.getFold step h key atKey elsewhere (Some kk) rest (step m kk vv) arest in
    match d: Ord.compare key kk with
      | Equal =>
        rewrite Map.Spec.lookupBelow key kk rest arest (z => Ordering.equalNotGreater (Eq.trans (Eq.sym d) z)),
          Eq.sym (ord.equal key kk d) in
        atKey m vv
      | Less =>
        Eq.cong (Map.Spec.atKey h (Map.Tree.lookupList key rest))
          (elsewhere m kk vv (Map.Spec.notEqualOfCompare key kk (z => Ordering.lessNotEqual (Eq.trans (Eq.sym d) z))))
      | Greater =>
        Eq.cong (Map.Spec.atKey h (Map.Tree.lookupList key rest))
          (elsewhere m kk vv (Map.Spec.notEqualOfCompare key kk (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym d) z))))

-- `unionWith`: the values there are, with `f` where both maps have one.
theorem Map.getUnionWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (a: Map k v) (b: Map k v):
    Map.get key (Map.unionWith f a b) = Option.merge f (Map.get key a) (Map.get key b) :=
  Eq.trans (Eq.cong (Map.get key) (Map.foldLeftToList (acc key2 value => Map.insertWith f key2 value acc) b a))
    (Eq.trans
      (Map.getFold (acc key2 value => Map.insertWith f key2 value acc) (value old => Some (Map.Tree.combine f value old)) key
        (m value => Map.getInsertWith f key value m) (m kk value ne => Map.getInsertWithOther f kk value key ne m)
        None (Map.toList a) b (Map.toListSorted a))
      (Eq.trans (Eq.cong (x => Map.Spec.atKey (value old => Some (Map.Tree.combine f value old)) x (Map.get key b)) (Eq.sym (Map.getToList key a)))
        (Map.Spec.atKeyCombine f (Map.get key a) (Map.get key b))))

-- Inserting into a raw map, then taking its class, is inserting into the class.
theorem Map.ofRawFoldInsert [auto ord: Ord k]: (xs: List (k, v)) -> (r: Map.Raw k v) ->
    Map.ofRaw (Map.Spec.foldLeft (acc key value => Map.Raw.insert key value acc) r xs)
      = Map.Spec.foldLeft (acc key value => Map.insert key value acc) (Map.ofRaw r) xs
  | Nil, r => rfl
  | Cons (kk, vv) rest, r => Map.ofRawFoldInsert rest (Map.Raw.insert kk vv r)

theorem Map.getUnionRaw [auto ord: Ord k] (key: k) (ra: Map.Raw k v) (rb: Map.Raw k v):
    Map.get key (Map.union (Map.ofRaw ra) (Map.ofRaw rb)) = Option.orElse (Map.Raw.get key ra) (Map.Raw.get key rb) :=
  Eq.trans (Eq.cong (r => Map.get key (Map.ofRaw r)) (Map.Raw.foldLeftToList (acc key2 value => Map.Raw.insert key2 value acc) rb ra))
    (Eq.trans (Eq.cong (Map.get key) (Map.ofRawFoldInsert (Map.Raw.toList ra) rb))
      (Eq.trans
        (Map.getFold (acc key2 value => Map.insert key2 value acc) (value old => Some value) key
          (m value => Map.getInsert key value m) (m kk value ne => Map.getInsertOther kk value key ne m)
          None (Map.Raw.toList ra) (Map.ofRaw rb) (Map.Raw.toListSorted ra))
        (Eq.trans (Eq.cong (x => Map.Spec.atKey (value old => Some value) x (Map.Raw.get key rb)) (Eq.sym (Map.Raw.getToList key ra)))
          (Map.Spec.atKeyFirst (Map.Raw.get key ra) (Map.Raw.get key rb)))))

-- `union`: the first map's value, else the second's.
theorem Map.getUnion [auto ord: Ord k] (key: k) (a: Map k v) (b: Map k v):
    Map.get key (Map.union a b) = Option.orElse (Map.get key a) (Map.get key b) :=
  Map.indRaw [p := a' => Map.get key (Map.union a' b) = Option.orElse (Map.get key a') (Map.get key b)]
    (ra =>
      Map.indRaw [p := b' => Map.get key (Map.union (Map.ofRaw ra) b') = Option.orElse (Map.get key (Map.ofRaw ra)) (Map.get key b')]
        (rb => Map.getUnionRaw key ra rb) b)
    a

-- What `Map.fromListWith f` keeps at `key`: each value with the key in turn,
-- combined by `f new old` with what was found before.
def Map.lookupWithOnto [auto ord: Ord k] (f: v -> v -> v) (key: k): Option v -> List (k, v) -> Option v
  | found, Nil => found
  | found, Cons (kk, vv) rest => match Ord.compare key kk with
    | Equal => Map.lookupWithOnto f key (Some (Map.Tree.combine f vv found)) rest
    | _ => Map.lookupWithOnto f key found rest

def Map.lookupWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (xs: List (k, v)): Option v := Map.lookupWithOnto f key None xs

theorem Map.getFoldInsertWith [auto ord: Ord k] (f: v -> v -> v) (key: k): (xs: List (k, v)) -> (m: Map k v) ->
    Map.get key (List.foldLeft (acc entry => Map.insertWith f entry.fst entry.snd acc) m xs) = Map.lookupWithOnto f key (Map.get key m) xs
  | Nil, m => rfl
  | Cons (kk, vv) rest, m =>
    rewrite Map.getFoldInsertWith f key rest (Map.insertWith f kk vv m) in
    match e: Ord.compare key kk with
      | Less => rewrite Map.getInsertWithOther f kk vv key (Map.Spec.notEqualOfCompare key kk (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) m in rfl
      | Equal => rewrite ord.equal key kk e, Map.getInsertWith f kk vv m in rfl
      | Greater => rewrite Map.getInsertWithOther f kk vv key (Map.Spec.notEqualOfCompare key kk (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) m in rfl

theorem Map.getFromListWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (xs: List (k, v)):
    Map.get key (Map.fromListWith f xs) = Map.lookupWith f key xs :=
  Map.getFoldInsertWith f key xs Map.empty

theorem Map.getOrCountStep [auto ord: Ord k] (key: k) (x: k) (m: Map k Nat):
    Map.getOr 0 key (Map.insertWith Nat.add x 1 m) = Nat.succIf (Map.getOr 0 key m) (Map.Spec.sameKey key x) :=
  match e: Ord.compare key x with
    | Equal =>
      rewrite ord.equal key x e, Map.getInsertWith Nat.add x 1 m in
      match c: Map.get x m with
        | None => rfl
        | Some n => rfl
    | Less => rewrite Map.getInsertWithOther Nat.add x 1 key (Map.Spec.notEqualOfCompare key x (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) m in rfl
    | Greater => rewrite Map.getInsertWithOther Nat.add x 1 key (Map.Spec.notEqualOfCompare key x (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) m in rfl

theorem Map.getOrFoldCount [auto ord: Ord k] (key: k): (xs: List k) -> (m: Map k Nat) ->
    Map.getOr 0 key (List.foldLeft (acc x => Map.insertWith Nat.add x 1 acc) m xs)
      = List.foldLeft (n x => Nat.succIf n (Map.Spec.sameKey key x)) (Map.getOr 0 key m) xs
  | Nil, m => rfl
  | Cons x rest, m =>
    Eq.trans (Map.getOrFoldCount key rest (Map.insertWith Nat.add x 1 m))
      (Eq.cong (n => List.foldLeft (n2 y => Nat.succIf n2 (Map.Spec.sameKey key y)) n rest) (Map.getOrCountStep key x m))

-- `counts`: how many elements compare equal to `key`.
theorem Map.getOrCounts [auto ord: Ord k] (key: k) (xs: List k): Map.getOr 0 key (Map.counts xs) = List.count (x => Map.Spec.sameKey key x) xs :=
  Map.getOrFoldCount key xs Map.empty

-- `groupBy`: the elements whose key is `kk`, in list order, if there are any.
theorem Map.getGroupBy [auto ord: Ord k] (key: a -> k) (kk: k): (xs: List a) ->
    Map.get kk (Map.groupBy key xs) = Map.Spec.nonEmpty (List.filter (x => Map.Spec.sameKey kk (key x)) xs)
  | Nil => rfl
  | Cons x rest =>
    match e: Ord.compare kk (key x) with
      | Equal =>
        rewrite ord.equal kk (key x) e, Map.getInsertWith List.append (key x) [x] (Map.groupBy key rest), Map.getGroupBy key (key x) rest in
        match c: List.filter (y => Map.Spec.sameKey (key x) (key y)) rest with
          | Nil => rfl
          | Cons y ys => rfl
      | Less =>
        rewrite Map.getInsertWithOther List.append (key x) [x] kk
          (Map.Spec.notEqualOfCompare kk (key x) (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) (Map.groupBy key rest) in
        Map.getGroupBy key kk rest
      | Greater =>
        rewrite Map.getInsertWithOther List.append (key x) [x] kk
          (Map.Spec.notEqualOfCompare kk (key x) (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) (Map.groupBy key rest) in
        Map.getGroupBy key kk rest

-- `indexBy`: the first element whose key is `kk`.
theorem Map.getIndexBy [auto ord: Ord k] (key: a -> k) (kk: k): (xs: List a) ->
    Map.get kk (Map.indexBy key xs) = List.find (x => Map.Spec.sameKey kk (key x)) xs
  | Nil => rfl
  | Cons x rest =>
    match e: Ord.compare kk (key x) with
      | Equal =>
        rewrite ord.equal kk (key x) e, Map.getInsertWith (newer older => newer) (key x) x (Map.indexBy key rest) in
        Eq.cong Some (Map.Tree.combineFirst x (Map.get (key x) (Map.indexBy key rest)))
      | Less =>
        rewrite Map.getInsertWithOther (newer older => newer) (key x) x kk
          (Map.Spec.notEqualOfCompare kk (key x) (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) (Map.indexBy key rest) in
        Map.getIndexBy key kk rest
      | Greater =>
        rewrite Map.getInsertWithOther (newer older => newer) (key x) x kk
          (Map.Spec.notEqualOfCompare kk (key x) (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) (Map.indexBy key rest) in
        Map.getIndexBy key kk rest

-- The same with `==`, as a program finding by key writes it.
theorem Map.getIndexByEq [auto ord: Ord k] (key: a -> k) (kk: k) (xs: List a):
    Map.get kk (Map.indexBy key xs) = List.find (x => key x == kk) xs :=
  Eq.trans (Map.getIndexBy key kk xs) (List.findCong (x => Map.Spec.sameKey kk (key x)) (x => key x == kk) xs (x => Map.Spec.sameKeyDecide kk (key x)))

-- What `indexBy` has under `kk` has key `kk`.
theorem Map.indexByKey [auto ord: Ord k] (key: a -> k) (kk: k) (xs: List a) (y: a) (h: Map.get kk (Map.indexBy key xs) = Some y): key y = kk :=
  match List.findSome (x => Map.Spec.sameKey kk (key x)) xs y (Eq.trans (Eq.sym (Map.getIndexBy key kk xs)) h) with
    | Both py m => Eq.sym (Map.Spec.sameKeySound kk (key y) py)

-- For text keys, `==` is `Text`'s own.
theorem Map.getIndexByText (key: a -> Text) (kk: Text) (xs: List a): Map.get kk (Map.indexBy key xs) = List.find (x => key x == kk) xs :=
  Map.getIndexByEq key kk xs

theorem Map.getMapWithKey [auto ord: Ord k] (f: k -> v -> w) (key: k) (m: Map k v):
    Map.get key (Map.mapWithKey f m) = Option.map (f key) (Map.get key m) :=
  Map.indRaw [p := m' => Map.get key (Map.mapWithKey f m') = Option.map (f key) (Map.get key m')] (r => Map.Raw.getMapWithKey f key r) m

-- `filterMap`: `f` of the value at `key`, if there is one.
theorem Map.getFilterMap [auto ord: Ord k] (f: k -> v -> Option w) (key: k) (m: Map k v):
    Map.get key (Map.filterMap f m) = Option.flatMap (f key) (Map.get key m) :=
  Eq.trans (Eq.cong (Map.get key) (Map.foldLeftToList (Map.filterMapStep f) Map.empty m))
    (Eq.trans
      (Map.getFold (Map.filterMapStep f) (value old => Option.orElse (f key value) old) key
        (acc value =>
          match c: f key value with
            | Some y => Map.getInsert key y acc
            | None => rfl)
        (acc kk value ne =>
          match c: f kk value with
            | Some y => Map.getInsertOther kk y key ne acc
            | None => rfl)
        None (Map.toList m) Map.empty (Map.toListSorted m))
      (Eq.trans (Eq.cong (x => Map.Spec.atKey (value old => Option.orElse (f key value) old) x None) (Eq.sym (Map.getToList key m)))
        (Map.Spec.atKeyFilterMap (f key) (Map.get key m))))

theorem Map.getIntersectWith [auto ord: Ord k] (f: v -> w -> x) (key: k) (a: Map k v) (b: Map k w):
    Map.get key (Map.intersectWith f a b) = Option.flatMap (value => Option.map (f value) (Map.get key b)) (Map.get key a) :=
  Map.getFilterMap (key2 value => Option.map (f value) (Map.get key2 b)) key a

theorem Map.getDifference [auto ord: Ord k] (key: k) (a: Map k v) (b: Map k w):
    Map.get key (Map.difference a b) = Option.filter (value => !(Map.contains key b)) (Map.get key a) :=
  Map.getFilter (key2 value => !(Map.contains key2 b)) key a

-- `range`: the value at `key` if `lo <= key < hi`.
theorem Map.getRange [auto ord: Ord k] (lo: k) (hi: k) (key: k) (m: Map k v):
    Map.get key (Map.range lo hi m) = (if !(Map.Spec.isLess key lo) && Map.Spec.isLess key hi then Map.get key m else None) :=
  rewrite Map.getFilter (key2 value => !(Map.Spec.isLess key2 lo) && Map.Spec.isLess key2 hi) key m in
  match c: !(Map.Spec.isLess key lo) && Map.Spec.isLess key hi with
    | True =>
      match d: Map.get key m with
        | None => rfl
        | Some value => rfl
    | False =>
      match d: Map.get key m with
        | None => rfl
        | Some value => rfl

-- `mapKeys`: the last entry, in key order, whose new key is `key`.
theorem Map.getMapKeys [auto ord: Ord j] (f: k -> j) (key: j) (m: Map k v [ord := o]):
    Map.get key (Map.mapKeys f m) = Map.lookupLast key (List.map (e => (f e.fst, e.snd)) (Map.toList m)) :=
  Map.getFromList key (List.map (e => (f e.fst, e.snd)) (Map.toList m))

-- Equations between maps

-- Inserting two different keys in either order gives the same map.
theorem Map.insertComm [auto ord: Ord k] (a: k) (x: v) (b: k) (y: v) (ne: Not (a = b)) (m: Map k v):
    (m |> Map.insert a x |> Map.insert b y) = (m |> Map.insert b y |> Map.insert a x) :=
  Map.ext ((m.insert a x).insert b y) ((m.insert b y).insert a x) (key =>
    match ord.eq.decide key b with
      | Yes hb =>
        rewrite hb in
        Eq.trans (Map.getInsert b y (m.insert a x))
          (Eq.sym (Eq.trans (Map.getInsertOther a x b (e => ne (Eq.sym e)) (m.insert b y)) (Map.getInsert b y m)))
      | No hb =>
        match ord.eq.decide key a with
          | Yes ha =>
            rewrite ha in
            Eq.trans (Eq.trans (Map.getInsertOther b y a ne (m.insert a x)) (Map.getInsert a x m))
              (Eq.sym (Map.getInsert a x (m.insert b y)))
          | No ha =>
            Eq.trans (Eq.trans (Map.getInsertOther b y key hb (m.insert a x)) (Map.getInsertOther a x key ha m))
              (Eq.sym (Eq.trans (Map.getInsertOther a x key ha (m.insert b y)) (Map.getInsertOther b y key hb m))))

-- Inserting the value a key already has changes nothing.
theorem Map.insertGet [auto ord: Ord k] (key: k) (value: v) (m: Map k v) (h: Map.get key m = Some value): Map.insert key value m = m :=
  Map.ext (m.insert key value) m (other =>
    match ord.eq.decide other key with
      | Yes e => rewrite e in Eq.trans (Map.getInsert key value m) (Eq.sym h)
      | No ne => Map.getInsertOther key value other ne m)

-- Inserting at a key twice keeps the second value.
theorem Map.insertInsert [auto ord: Ord k] (key: k) (x: v) (y: v) (m: Map k v):
    (m |> Map.insert key x |> Map.insert key y) = Map.insert key y m :=
  Map.ext ((m.insert key x).insert key y) (m.insert key y) (other =>
    match ord.eq.decide other key with
      | Yes e => rewrite e in Eq.trans (Map.getInsert key y (m.insert key x)) (Eq.sym (Map.getInsert key y m))
      | No ne =>
        Eq.trans (Map.getInsertOther key y other ne (m.insert key x))
          (Eq.trans (Map.getInsertOther key x other ne m) (Eq.sym (Map.getInsertOther key y other ne m))))

-- Removing a key just inserted removes it from the map before.
theorem Map.removeInsert [auto ord: Ord k] (key: k) (value: v) (m: Map k v):
    (m |> Map.insert key value |> Map.remove key) = Map.remove key m :=
  Map.ext ((m.insert key value).remove key) (m.remove key) (other =>
    match ord.eq.decide other key with
      | Yes e => rewrite e in Eq.trans (Map.getRemove key (m.insert key value)) (Eq.sym (Map.getRemove key m))
      | No ne =>
        Eq.trans (Map.getRemoveOther key other ne (m.insert key value))
          (Eq.trans (Map.getInsertOther key value other ne m) (Eq.sym (Map.getRemoveOther key other ne m))))

-- Induction over maps

-- `Map.induction` on the map whose entries are `xs`: take the first entry
-- off, and the rest is the smaller map it was inserted into.
theorem Map.inductionToList [auto ord: Ord k] [p: Map k v -> Prop] (base: p Map.empty)
    (step: (key: k) -> (value: v) -> (m: Map k v) -> p m -> Map.get key m = None -> p (Map.insert key value m)):
    (xs: List (k, v)) -> (m: Map k v) -> Map.toList m = xs -> p m
  | Nil, m, h => rewrite Map.toListInjective m Map.empty h in base
  | Cons (kk, vv) rest, m, h =>
    let found: Map.get kk m = Some vv :=
      Eq.trans (Map.getToList kk m) (Eq.trans (Eq.cong (Map.Tree.lookupList kk) h) (Map.Spec.lookupHead kk vv rest))
    let back: Map.insert kk vv (Map.remove kk m) = m :=
      Map.ext ((m.remove kk).insert kk vv) m (other =>
        match ord.eq.decide other kk with
          | Yes e => rewrite e in Eq.trans (Map.getInsert kk vv (m.remove kk)) (Eq.sym found)
          | No ne => Eq.trans (Map.getInsertOther kk vv other ne (m.remove kk)) (Map.getRemoveOther kk other ne m))
    let smaller: Map.toList (Map.remove kk m) = rest :=
      Eq.trans (Map.toListRemove kk m) (Eq.trans (Eq.cong (Map.Spec.remove kk) h) (Map.Spec.removeEqual kk kk vv rest (Ord.compareSelf kk)))
    rewrite Eq.sym back in
    step kk vv (Map.remove kk m) (Map.inductionToList [p := p] base step rest (Map.remove kk m) smaller) (Map.getRemove kk m)

-- To prove something of every map, prove it of the empty map, and of a map
-- with a new key inserted, given it of the map before.
theorem Map.induction [auto ord: Ord k] [p: Map k v -> Prop] (base: p Map.empty)
    (step: (key: k) -> (value: v) -> (m: Map k v) -> p m -> Map.get key m = None -> p (Map.insert key value m)) (m: Map k v): p m :=
  Map.inductionToList [p := p] base step (Map.toList m) m rfl

def Map.example: Map Nat Text := Map.fromList [(3, "c"), (1, "a"), (2, "b")]

test "map: toList is in key order" := Map.toList Map.example == [(1, "a"), (2, "b"), (3, "c")]
test "map: get" := Map.get 2 Map.example == Some "b" && Map.get 4 Map.example == None
test "map: getOr" := Map.getOr "?" 4 Map.example == "?"
test "map: contains" := Map.contains 1 Map.example && !(Map.contains 0 Map.example)
test "map: insert replaces" := Map.toList (Map.insert 2 "B" Map.example) == [(1, "a"), (2, "B"), (3, "c")]
test "map: insertWith counts" :=
  Map.toList (List.foldLeft (m c => Map.insertWith Nat.add c 1 m) Map.empty ['b', 'a', 'b']) == [('a', 1), ('b', 2)]
test "map: remove" := Map.toList (Map.remove 2 Map.example) == [(1, "a"), (3, "c")] && Map.size (Map.remove 9 Map.example) == 3
test "map: alter" := Map.toList (Map.alter (old => None) 1 (Map.alter (old => Some "d") 4 Map.example)) == [(2, "b"), (3, "c"), (4, "d")]
test "map: adjust" := Map.get 3 (Map.adjust (t => Text.append t "!") 3 Map.example) == Some "c!"
test "map: size" := Map.size Map.example == 3 && Map.isEmpty (Map.empty: Map Nat Nat)
test "map: size after insert and remove" :=
  Map.size (Map.insert 2 "B" Map.example) == 3 && Map.size (Map.insert 4 "d" Map.example) == 4
    && Map.size (Map.remove 2 Map.example) == 2 && Map.size (Map.remove 4 Map.example) == 3
    && Map.size (Map.remove 1 (Map.empty: Map Nat Nat)) == 0
test "map: toList holds what get finds" := List.all (e => Map.get e.fst Map.example == Some e.snd) (Map.toList Map.example)
test "map: keys and values" := Map.keys Map.example == [1, 2, 3] && Map.values Map.example == ["a", "b", "c"]
test "map: fromList, later wins" := Map.toList (Map.fromList [(1, 1), (1, 2)]) == [(1, 2)]
test "map: foldLeft" := Map.foldLeft (acc key t => acc + key) 0 Map.example == 6
test "map: map" := Map.values (Map.map Text.length Map.example) == [1, 1, 1]
test "map: get after map" := Map.get 2 (Map.map Text.length Map.example) == Some 1 && Map.get 4 (Map.map Text.length Map.example) == None
test "map: filter" := Map.keys (Map.filter (key t => Nat.leq 2 key) Map.example) == [2, 3]
test "map: union" := Map.toList (Map.union (Map.singleton 1 "x") Map.example) == [(1, "x"), (2, "b"), (3, "c")]
test "map: show" := "${Map.example}" == "Map.fromList [(1, \"a\"), (2, \"b\"), (3, \"c\")]"
test "map: equal in any order" :=
  Map.example == Map.fromList [(1, "a"), (2, "b"), (3, "c")] && Map.example != Map.insert 2 "B" Map.example
test "map: ordered by entries" := Map.insert 2 "B" Map.example < Map.example && Map.example <= Map.fromList [(2, "b"), (1, "a"), (3, "c")]

def Map.example2: Map Nat Text := Map.fromList [(3, "c"), (1, "a"), (2, "b"), (7, "g"), (5, "e")]

test "map: fromListWith combines in list order" :=
  Map.toList (Map.fromListWith (new old => Text.append old new) [(1, "a"), (2, "b"), (1, "c")]) == [(1, "ac"), (2, "b")]
test "map: groupBy keeps list order" := Map.toList (Map.groupBy (n => n % 3) [1, 2, 3, 4, 5, 6]) == [(0, [3, 6]), (1, [1, 4]), (2, [2, 5])]
test "map: indexBy keeps the first" := Map.toList (Map.indexBy Text.length ["ab", "c", "de", "f"]) == [(1, "c"), (2, "ab")]
test "map: indexBy empty" := Map.toList (Map.indexBy Text.length Nil) == Nil
test "map: counts" := Map.toList (Map.counts ['b', 'a', 'b']) == [('a', 1), ('b', 2)]
test "map: find" := Map.find (key t => key > 2) Map.example2 == Some (3, "c") && Map.find (key t => key > 7) Map.example2 == None
test "map: min and max" :=
  Map.min Map.example2 == Some (1, "a") && Map.max Map.example2 == Some (7, "g") && Map.min (Map.empty: Map Nat Nat) == None
test "map: below" :=
  Map.below 5 Map.example2 == Some (3, "c") && Map.below 6 Map.example2 == Some (5, "e") && Map.below 1 Map.example2 == None
    && Map.below 100 Map.example2 == Some (7, "g")
test "map: above" :=
  Map.above 5 Map.example2 == Some (7, "g") && Map.above 0 Map.example2 == Some (1, "a") && Map.above 7 Map.example2 == None
    && Map.above 4 Map.example2 == Some (5, "e")
test "map: unionWith" := Map.toList (Map.unionWith Nat.add (Map.fromList [(1, 10), (2, 20)]) (Map.fromList [(2, 1), (3, 1)])) == [(1, 10), (2, 21), (3, 1)]
test "map: intersectWith" := Map.toList (Map.intersectWith (t n => n) Map.example2 (Map.fromList [(2, 20), (4, 40), (5, 50)])) == [(2, 20), (5, 50)]
test "map: difference" := Map.keys (Map.difference Map.example2 (Map.fromList [(2, ()), (5, ())])) == [1, 3, 7]
test "map: mapWithKey" :=
  Map.toList (Map.mapWithKey (key t => Text.append t (Nat.toText key)) Map.example2) == [(1, "a1"), (2, "b2"), (3, "c3"), (5, "e5"), (7, "g7")]
test "map: filterMap" := Map.toList (Map.filterMap (key t => if key > 2 then Some key else None) Map.example2) == [(3, 3), (5, 5), (7, 7)]
test "map: partition" :=
  Map.keys (Map.partition (key t => key > 2) Map.example2).fst == [3, 5, 7] && Map.keys (Map.partition (key t => key > 2) Map.example2).snd == [1, 2]
test "map: mapKeys, later wins" := Map.toList (Map.mapKeys (key => key / 2) Map.example2) == [(0, "a"), (1, "c"), (2, "e"), (3, "g")]
test "map: foldRight" := Map.foldRight (key t acc => Text.append t acc) "" Map.example2 == "abceg"
test "map: any, all, count" :=
  Map.any (key t => key == 5) Map.example2 && !(Map.all (key t => key < 7) Map.example2) && Map.count (key t => key > 2) Map.example2 == 3
test "map: range" := Map.keys (Map.range 2 6 Map.example2) == [2, 3, 5] && Map.keys (Map.range 6 2 Map.example2) == Nil
