--| `Map k v`: finite maps from keys to values, with the ordering of the keys
--| in the map's type: `Map Text Nat` is `Map Text Nat [ord := Text.instOrd]`,
--| and a map built with another ordering has another type. A map is a
--| quotient: its representative is a `Map.Raw`, a weight-balanced search tree
--| (std/Map/Raw.sw), and two representatives with the same entries in key
--| order are the same map. So `m = n` exactly when `m` and `n` have the same
--| entries ([`Map.eqIffToListEq`]), for any type of values, and `==` compares
--| the entries. Each operation is the raw one, lifted with the lemma that it
--| respects `Map.Raw.Equiv` (std/Map/Spec.sw). At run time a map is its tree,
--| in one record.
--| Insertion, lookup and removal take O(log n) comparisons; `size` is O(1).
--| `union`, `unionWith`, `intersectWith`, `difference` and `filter` are O(n +
--| m), by merging sorted entry lists (std/Map/Spec.sw, "Bulk operations").
-- (docs/proposals/interfaces.md §7.5, D169)
-- (docs/proposals/map-equality.md §8)
-- docs/proposals/map-set.md.

import Std (Eq)

--| A finite map from keys to values, ordered by the keys: `Map Text Nat` maps texts to numbers.
--| It is a record around the quotient, so that dot notation on a map finds `Map`'s
--| functions (`m.insert 3 "c"`).
type Map (k: Type) (v: Type) [auto ord: Ord k] = { raw: Quot (Map.Raw k v [ord := ord]) Map.Raw.Equiv }

--| The map whose entries are the raw map's.
def Map.ofRaw (rawMap: Map.Raw k v [ord := o]): Map k v [ord := o] := { raw = Quot.mk rawMap }

--| To prove something of every map, prove it of the map of every raw map.
theorem Map.indRaw [p: Map k v [ord := o] → Prop] (h: ∀ (r: Map.Raw k v [ord := o]) => p (Map.ofRaw r))
    (m: Map k v [ord := o]): p m :=
  match m with
    | { raw = q } => Quot.ind [p := q' => p { raw = q' }] h q

-- Building

--| The map with no entries.
def Map.empty [auto ord: Ord k]: Map k v := Map.ofRaw Map.Raw.empty

--| The map with one entry, `value` at `key`.
def Map.singleton [auto ord: Ord k] (key: k) (value: v): Map k v := Map.ofRaw (Map.Raw.singleton key value)

--| A map of the pairs; a later pair's value replaces an earlier one's ([`Map.getFromList`]).
--| O(n log n), or O(n) when the keys come in ascending order.
def Map.fromList [auto ord: Ord k] (xs: List (k, v)): Map k v := Map.ofRaw (Map.Raw.fromListFast xs)

--| A map of the pairs, a later pair's value replacing an earlier one's:
--| `Map.fromList` with the list first, so `[(1, "a")].toMap` reads as a
--| method ([`List.toMapFromList`]).
def List.toMap [auto ord: Ord k] (items: List (k, v)): Map k v := Map.fromList items

-- Reading

--| The entries, in key order ([`Map.toListSorted`]), each key once ([`Map.keysDistinct`]).
def Map.toList (m: Map k v [ord := o]): List (k, v) := Quot.lift Map.Raw.toList (a b same => same) m.raw

--| The value at `key`, if there is one.
def Map.get [auto ord: Ord k] (m: Map k v) (key: k): Option v :=
  Quot.lift (Map.Raw.get key) (a b same => Map.Raw.getRespects key a b same) m.raw

--| The value at `key`, or `fallback`.
def Map.getOr [auto ord: Ord k] (m: Map k v) (key: k) (fallback: v): v := m.get key |> .getOrElse fallback

--| Whether the map has an entry at `key`.
def Map.contains [auto ord: Ord k] (m: Map k v) (key: k): Bool := match Map.get m key with
  | Some _ => True
  | None => False

--| The number of entries, O(1): the length of `Map.toList` ([`Map.sizeToList`]).
def Map.size (m: Map k v [ord := o]): Nat := Quot.lift Map.Raw.size (a b same => Map.Raw.sizeRespects a b same) m.raw

--| Whether the map has no entries.
def Map.isEmpty (m: Map k v [ord := o]): Bool := Nat.equal m.size 0

--| The keys, in order, each once ([`Map.keysDistinct`]); there are `Map.size` of them ([`Map.lengthKeys`]).
def Map.keys (m: Map k v [ord := o]): List k := m.toList.map Pair.fst

--| The values, in the order of their keys.
def Map.values (m: Map k v [ord := o]): List v := m.toList.map Pair.snd

--| Left fold over the entries in key order: `f (f initial k1 v1) k2 v2`.
def Map.foldLeft (m: Map k v [ord := o]) (initial: b) (f: b → k → v → b): b :=
  Quot.lift (Map.Raw.foldLeft f initial) (a b same => Map.Raw.foldLeftRespects f initial a b same) m.raw

-- Changing

--| `value` at `key`; if `key` has a value already, `f value old` (so
--| `Map.insertWith counts key 1 Nat.add` counts; [`Map.getInsertWith`]).
def Map.insertWith [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (f: v → v → v): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.insertWith f key value rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.insertWithRespects f key value a b same))
    m.raw
}

--| `value` at `key`, replacing any value there ([`Map.getInsert`]); other keys keep theirs ([`Map.getInsertOther`]).
def Map.insert [auto ord: Ord k] (m: Map k v) (key: k) (value: v): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.insert key value rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.insertRespects key value a b same))
    m.raw
}

--| Without `key` (the same map if it isn't there): [`Map.getRemove`], [`Map.getRemoveOther`].
def Map.remove [auto ord: Ord k] (m: Map k v) (key: k): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.remove key rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.removeRespects key a b same))
    m.raw
}

--| The value at `key` changed by `f`, which sees `None` when there's none
--| and removes the entry by returning `None` ([`Map.getAlter`]).
def Map.alter [auto ord: Ord k] (m: Map k v) (key: k) (f: Option v → Option v): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.alter f key rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.alterRespects f key a b same))
    m.raw
}

--| The value at `key` changed by `f`, if there is one ([`Map.getAdjust`]).
def Map.adjust [auto ord: Ord k] (m: Map k v) (key: k) (f: v → v): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.adjust f key rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.adjustRespects f key a b same))
    m.raw
}

--| Every value changed by `f`; the keys stay ([`Map.getMap`]).
def Map.map (m: Map k v [ord := o]) (f: v → w): Map k w [ord := o] := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.map f rawMap): Quot (Map.Raw k w [ord := o]) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.mapRespects f a b same))
    m.raw
}

--| The entries for which `p` holds ([`Map.getFilter`]).
def Map.filter [auto ord: Ord k] (m: Map k v) (p: k → v → Bool): Map k v := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.filter p rawMap): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.filterRespects p a b same))
    m.raw
}

--| `Map.liftBinary` with its first argument a raw map.
def Map.liftBinaryRaw [auto ord: Ord k] (op: Map.Raw k v [ord := ord] → Map.Raw k w [ord := ord] → Map.Raw k x [ord := ord])
    (respects: ∀ (a a2: Map.Raw k v) (b b2: Map.Raw k w) =>
    Map.Raw.Equiv a a2 → Map.Raw.Equiv b b2 → Map.Raw.Equiv (op a b) (op a2 b2))
    (a: Map.Raw k v) (q: Quot (Map.Raw k w) Map.Raw.Equiv): Quot (Map.Raw k x) Map.Raw.Equiv :=
  Quot.lift
    (b => (Quot.mk (op a b): Quot (Map.Raw k x) Map.Raw.Equiv))
    (b b2 same => Quot.sound (respects a a b b2 rfl same))
    q

--| A raw operation on two maps that gives equivalent results for equivalent
--| arguments, as an operation on maps.
@[noReceiver]
def Map.liftBinary [auto ord: Ord k] (op: Map.Raw k v [ord := ord] → Map.Raw k w [ord := ord] → Map.Raw k x [ord := ord])
    (respects: ∀ (a a2: Map.Raw k v) (b b2: Map.Raw k w) =>
    Map.Raw.Equiv a a2 → Map.Raw.Equiv b b2 → Map.Raw.Equiv (op a b) (op a2 b2))
    (a: Map k v) (b: Map k w): Map k x := {
  raw = Quot.lift
    (rawMap => Map.liftBinaryRaw op respects rawMap b.raw)
    (a1 a2 same =>
      Quot.ind
        [p := q => Map.liftBinaryRaw op respects a1 q = Map.liftBinaryRaw op respects a2 q]
        (rawMap => Quot.sound (respects a1 a2 rawMap rawMap same rfl))
        b.raw)
    a.raw
}

--| Both maps' entries; where both have a key, the first map's value ([`Map.getUnion`]).
--| O(n + m) by merging the entry lists, or O(n log m) when one map, of n
--| entries, is much smaller (likewise `unionWith` and `difference`, and
--| `intersectWith` when the first map is the smaller).
def Map.union [auto ord: Ord k] (a: Map k v) (b: Map k v): Map k v := Map.liftBinary Map.Raw.union Map.Raw.unionRespects a b

-- More building

--| A map of the pairs; where a key comes again, `f new old` combines its
--| values, in list order (`Map.fromListWith xs Nat.add` sums them; [`Map.getFromListWith`]).
def Map.fromListWith [auto ord: Ord k] (xs: List (k, v)) (f: v → v → v): Map k v :=
  List.foldLeft xs Map.empty (m entry => Map.insertWith m entry.fst entry.snd f)

--| The elements under their keys, each group in list order and never empty:
--| `Map.groupBy [1, 2, 3] (n => n % 2)` is `Map.fromList [(0, [2]), (1, [1, 3])]`
--| ([`Map.getGroupBy`]).
def Map.groupBy [auto ord: Ord k] (xs: List a) (key: a → k): Map k (NonEmptyList a) :=
  List.foldRight xs Map.empty (x m => Map.insertWith m (key x) (NonEmptyList.singleton x) NonEmptyList.append)

--| `Map.groupBy` with the list first, so `[1, 2, 3].groupBy (n => n % 2)` reads
--| as a method: it is `Map.fromList [(0, [2]), (1, [1, 3])]`, each group in
--| list order and never empty ([`Map.groupBy`], [`Map.getGroupBy`]).
def List.groupBy [auto ord: Ord k] (xs: List a) (key: a → k): Map k (NonEmptyList a) := Map.groupBy xs key

--| The values of the elements under their keys, each group in list order and
--| never empty: `[("a", 1), ("b", 2), ("a", 3)].groupMap Pair.fst Pair.snd` is
--| `Map.fromList [("a", [1, 3]), ("b", [2])]`, so it inverts a relation. The
--| empty list gives `Map.empty`; each insert is O(log n), so O(n log n) for
--| `n` elements ([`Map.groupBy`], [`Map.getGroupMap`]).
def Map.groupMap [auto ord: Ord k] (xs: List a) (key: a → k) (value: a → v): Map k (NonEmptyList v) :=
  List.foldRight xs Map.empty (x m => Map.insertWith m (key x) (NonEmptyList.singleton (value x)) NonEmptyList.append)

--| `Map.groupMap` with the list first, so `[("a", 1), ("b", 2)].groupMap
--| Pair.fst Pair.snd` reads as a method: each key with the values of the
--| elements having it, in list order and never empty ([`Map.groupMap`],
--| [`Map.getGroupMap`]).
def List.groupMap [auto ord: Ord k] (xs: List a) (key: a → k) (value: a → v): Map k (NonEmptyList v) := Map.groupMap xs key value

--| Each element under its key, the first where elements share a key ([`Map.getIndexBy`]).
--| `Map.indexBy ["ab", "c", "de"] Text.length` is `Map.fromList [(1, "c"), (2, "ab")]`.
--| A left fold (a loop), where the older value wins.
def Map.indexBy [auto ord: Ord k] (xs: List a) (key: a → k): Map k a :=
  List.foldLeft xs Map.empty (index element => Map.insertWith index (key element) element (newer older => older))

--| How many times each element occurs: `(Map.counts xs).getOr x 0` is `xs.count (== x)` ([`Map.getOrCounts`]).
def Map.counts [auto ord: Ord k] (xs: List k): Map k Nat := List.foldLeft xs Map.empty (m x => Map.insertWith m x 1 Nat.add)

-- More looking up

--| The first entry, in key order, for which `p` holds.
def Map.find (m: Map k v [ord := o]) (p: k → v → Bool): Option (k, v) := m.toList.find (e => p e.fst e.snd)

--| The entry with the smallest key, O(log n): the first of `Map.toList` ([`Map.minToList`]).
def Map.min (m: Map k v [ord := o]): Option (k, v) := Quot.lift Map.Raw.min (a b same => Map.Raw.minRespects a b same) m.raw

--| The entry with the smallest key and the map without it, in one walk,
--| O(log n): `min` and `remove` together ([`Map.popMinSpec`]).
def Map.popMin (m: Map k v [ord := o]): Option ((k, v), Map k v [ord := o]) :=
  Quot.lift Map.popMinRaw (a b same => Map.popMinRespects a b same) m.raw

--| `Map.popMin` of one representative.
def Map.popMinRaw (rawMap: Map.Raw k v [ord := o]): Option ((k, v), Map k v [ord := o]) :=
  Option.map (Map.Raw.popMin rawMap) (view => (view.fst, Map.ofRaw view.snd))

--| The entry with the largest key, O(log n): the last of `Map.toList` ([`Map.maxToList`]).
def Map.max (m: Map k v [ord := o]): Option (k, v) := Quot.lift Map.Raw.max (a b same => Map.Raw.maxRespects a b same) m.raw

--| The entry with the largest key below `key` (strictly), O(log n) ([`Map.belowToList`]).
def Map.below [auto ord: Ord k] (m: Map k v) (key: k): Option (k, v) :=
  Quot.lift (Map.Raw.below key) (a b same => Map.Raw.belowRespects key a b same) m.raw

--| The entry with the smallest key above `key` (strictly), O(log n).
def Map.above [auto ord: Ord k] (m: Map k v) (key: k): Option (k, v) :=
  Quot.lift (Map.Raw.above key) (a b same => Map.Raw.aboveRespects key a b same) m.raw

-- More combining

--| Both maps' entries; where both have a key, `f` of the first map's value
--| and the second's ([`Map.getUnionWith`]).
def Map.unionWith [auto ord: Ord k] (a: Map k v) (b: Map k v) (f: v → v → v): Map k v :=
  Map.liftBinary (Map.Raw.unionWith f) (Map.Raw.unionWithRespects f) a b

--| The keys of both maps, with `f` of their values ([`Map.getIntersectWith`]).
def Map.intersectWith [auto ord: Ord k] (a: Map k v) (b: Map k w) (f: v → w → x): Map k x :=
  Map.liftBinary (Map.Raw.intersectWith f) (Map.Raw.intersectWithRespects f) a b

--| The entries of `a` whose keys aren't in `b` ([`Map.getDifference`]).
def Map.difference [auto ord: Ord k] (a: Map k v) (b: Map k w): Map k v := Map.liftBinary Map.Raw.difference Map.Raw.differenceRespects a b

-- More transforming

--| Every value changed by `f`, which also sees its key; the keys stay ([`Map.getMapWithKey`]).
def Map.mapWithKey (m: Map k v [ord := o]) (f: k → v → w): Map k w [ord := o] := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.mapWithKey f rawMap): Quot (Map.Raw k w [ord := o]) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.mapWithKeyRespects f a b same))
    m.raw
}

--| The values `f` keeps, changed; `f` sees each key and value ([`Map.getFilterMap`]). O(n).
def Map.filterMap [auto ord: Ord k] (m: Map k v) (f: k → v → Option w): Map k w := {
  raw = Quot.lift
    (rawMap => (Quot.mk (Map.Raw.mapMaybe f rawMap): Quot (Map.Raw k w) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.mapMaybeRespects f a b same))
    m.raw
}

--| The entries for which `p` holds, and those for which it doesn't.
def Map.partition [auto ord: Ord k] (m: Map k v) (p: k → v → Bool): (Map k v, Map k v) :=
  (Map.filter m p, Map.filter m (key value => ¬(p key value)))

--| Every key changed by `f`, into a map ordered by `j`'s ordering; where two
--| keys go to one, the later (larger) key's value wins ([`Map.getMapKeys`]).
def Map.mapKeys [auto ord: Ord j] (m: Map k v [ord := o]) (f: k → j): Map j v :=
  m.toList.map (e => (f e.fst, e.snd)) |> .toMap

-- More reading

--| Right fold over the entries in key order: `f k1 v1 (f k2 v2 initial)`.
def Map.foldRight (m: Map k v [ord := o]) (initial: b) (f: k → v → b → b): b := m.toList.foldRight initial (e acc => f e.fst e.snd acc)

--| Whether some entry satisfies `p`.
def Map.any (m: Map k v [ord := o]) (p: k → v → Bool): Bool := m.toList.any (e => p e.fst e.snd)

--| Whether every entry satisfies `p`.
def Map.all (m: Map k v [ord := o]) (p: k → v → Bool): Bool := m.toList.all (e => p e.fst e.snd)

--| The number of entries satisfying `p`.
def Map.count (m: Map k v [ord := o]) (p: k → v → Bool): Nat := m.toList.count (e => p e.fst e.snd)

--| The entries with `lo <= key < hi` ([`Map.getRange`]).
def Map.range [auto ord: Ord k] (m: Map k v) (lo: k) (hi: k): Map k v :=
  Map.filter m (key value => ¬(Map.Spec.isLess key lo) ∧ Map.Spec.isLess key hi)

-- Equality: the same entries

--| Two classes with the same entries are the same class.
theorem Map.rawInjective (p: Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv) (q: Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv):
    Map.toList { raw = p } = Map.toList { raw = q } → p = q :=
  let motive: Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv → Prop :=
    p' => (q': Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv) → Map.toList { raw = p' } = Map.toList { raw = q' } → p' = q'
  let fromMk: (a: Map.Raw k v [ord := o]) → motive (Quot.mk a) :=
    a q' =>
      Quot.ind
        [p := q'' => Map.toList { raw = Quot.mk a } = Map.toList { raw = q'' } → Quot.mk a = q'']
        (b same => Quot.sound same)
        q'
  Quot.ind [p := motive] fromMk p q

--| Maps with the same entries are equal, whatever their values' type.
theorem Map.toListInjective (m n: Map k v [ord := o]) (same: Map.toList m = Map.toList n): m = n :=
  match m, n with
    | { raw = p }, { raw = q } => Eq.cong (r => ({ raw = r }: Map k v [ord := o])) (Map.rawInjective p q same)

--| Equal maps have the same entries, and maps with the same entries are equal.
theorem Map.eqIffToListEq (m: Map k v [ord := o]) (n: Map k v [ord := o]): (m = n) ↔ (Map.toList m = Map.toList n) := {
  forward = same => Eq.cong Map.toList same,
  backward = Map.toListInjective m n
}

--| The entries are in strictly increasing key order, and `get` looks a key up
--| in them.
theorem Map.toListSorted (m: Map k v [ord := o]): Map.Spec.Sorted o (Map.toList m) :=
  Map.indRaw [p := m' => Map.Spec.Sorted o (Map.toList m')] (r => Map.Raw.toListSorted r) m

--| No key appears twice.
theorem Map.keysDistinct (m: Map k v [ord := o]): List.Distinct (Map.keys m) := Map.Spec.keysDistinct o None (Map.toList m) (Map.toListSorted m)

theorem Map.getToList [auto ord: Ord k] (m: Map k v) (key: k): Map.get m key = Map.Tree.lookupList key (Map.toList m) :=
  Map.indRaw [p := m' => Map.get m' key = Map.Tree.lookupList key (Map.toList m')] (r => Map.Raw.getToList key r) m

--| An entry is in `toList` exactly when `get` finds it.
theorem Map.memToList [auto ord: Ord k] (m: Map k v) (key: k) (value: v): (List.Mem (key, value) (Map.toList m)) ↔ (Map.get m key = Some value) := {
  forward = mem => Eq.trans (Map.getToList m key) (Map.Spec.lookupOfMem key value None (Map.toList m) (Map.toListSorted m) mem),
  backward = found => Map.Spec.memOfLookup key value (Map.toList m) (Eq.trans (Eq.sym (Map.getToList m key)) found)
}

--| A key is among the keys exactly when the map contains it.
theorem Map.containsOfGet [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (h: Map.get m key = Some value): Map.contains m key = True :=
  rewrite h in rfl

theorem Map.containsOfMemToList [auto ord: Ord k] (m: Map k v) (key: k) (e: (k, v)) (inList: List.Mem e (Map.toList m)) (same: Pair.fst e = key): Map.contains m key = True :=
  match e with
    | (k1, v1) => rewrite <- same in Map.containsOfGet m k1 v1 ((Map.memToList m k1 v1).forward inList)

theorem Map.memKeysOfContains [auto ord: Ord k] (m: Map k v) (key: k) (h: Map.contains m key = True): List.Mem key (Map.keys m) :=
  match c: Map.get m key with
    | Some value => List.memMap (Map.toList m) (key, value) ((Map.memToList m key value).backward c) Pair.fst

theorem Map.memKeys [auto ord: Ord k] (m: Map k v) (key: k): List.Mem key (Map.keys m) ↔ Map.contains m key = True := {
  forward = inKeys =>
    List.anyElim (e => Pair.fst e = key) (Map.contains m key = True) (Map.toList m) (List.memMapAny (Map.toList m) Pair.fst key inKeys)
      (e inList same => Map.containsOfMemToList m key e inList same),
  backward = Map.memKeysOfContains m key
}

--| `m.contains key` reads as `key` being one of the map's keys, so a fact
--| `m.contains key = True` is taken apart as `key ∈ m.keys` and built from one.
@[reading]
theorem Map.containsReads [auto ord: Ord k] (m: Map k v) (key: k): (Map.contains m key = True) ↔ (key ∈ Map.keys m) :=
  { forward = (Map.memKeys m key).backward, backward = (Map.memKeys m key).forward }

--| `m.contains key = False` reads as `key` not being one of the map's keys.
@[reading]
theorem Map.containsReadsFalse [auto ord: Ord k] (m: Map k v) (key: k): (Map.contains m key = False) ↔ key ∉ Map.keys m := {
  forward = h m2 => Bool.falseNotTrue (Eq.trans (Eq.sym h) ((Map.memKeys m key).forward m2)),
  backward = no =>
    match c: Map.contains m key with
      | True => Void.exfalso (no ((Map.memKeys m key).backward c))
      | False => rfl
}

--| Maps that agree on every key are equal, whatever their values' type.
theorem Map.ext (m: Map k v [ord := o]) (n: Map k v [ord := o]) (h: ∀ (key: k) => Map.get m key = Map.get n key): m = n :=
  Map.toListInjective m n
    (Map.Spec.extLookup None (Map.toList m) (Map.toList n) (Map.toListSorted m) (Map.toListSorted n)
      (key => Eq.trans (Eq.sym (Map.getToList m key)) (Eq.trans (h key) (Map.getToList n key))))

--| `==`: compare the entry lists, the keys by the map's ordering. The branch
--| is chosen by the list comparison; `Quot.sound` is only inside the yes
--| proof, so `==` computes.
def Map.decEq [auto dv: DecEq v] (m: Map k v [ord := o]) (n: Map k v [ord := o]): Decidable (m = n) :=
  Decidable.elim (List.decEq (Pair.decEq o.eq.decide dv.decide) (Map.toList m) (Map.toList n))
    (same => Decidable.yes (Map.toListInjective m n same))
    (differ => Decidable.no (same => differ (Eq.cong Map.toList same)))

--| `==` on maps: the same entries.
instance Map.instDecEq [auto dv: DecEq v]: DecEq (Map k v [ord := o]) := { decide = Map.decEq }

--| `compare`: the entry lists, lexicographically, the keys by the map's
--| ordering.
-- Each law comes from the list order's, `equal` through `toListInjective`.
def Map.compare [auto vord: Ord v] (m: Map k v [ord := o]) (n: Map k v [ord := o]): Ordering :=
  List.compareLex (Pair.compareWith o.compare vord.compare) (Map.toList m) (Map.toList n)

--| Maps in the order of their entry lists, lexicographically (`Map.compare`).
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

--| `Map.fromList [(1, "a"), (2, "b")]`, in key order, whatever the ordering.
instance Map.instShow [auto showK: Show k] [auto showV: Show v]: Show (Map k v [ord := o]) :=
  Show.fromText (m => Text.append "Map.fromList "
    (Show.list (p => Pair.showWith (x => Show.toSource x) (y => Show.toSource y) p) (Map.toList m)))

-- What each operation does to the entries (the raw maps' lemmas, for every
-- map)

theorem Map.toListEmpty [auto ord: Ord k]: Map.toList (Map.empty: Map k v) = [] := rfl

theorem Map.toListSingleton [auto ord: Ord k] (key: k) (value: v): Map.toList (Map.singleton key value: Map k v) = [(key, value)] := rfl

theorem Map.toListFromList [auto ord: Ord k] (xs: List (k, v)): Map.toList (Map.fromList xs: Map k v) = Map.Spec.fromList xs :=
  Map.Raw.toListFromListFast xs

theorem List.toMapFromList [auto ord: Ord k] (items: List (k, v)): items.toMap = Map.fromList items := rfl

theorem Map.toListInsertWith [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (f: v → v → v):
    Map.toList (Map.insertWith m key value f) = Map.Spec.insertWith f key value (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.insertWith m' key value f) = Map.Spec.insertWith f key value (Map.toList m')]
    (r => Map.Raw.toListInsertWith f key value r) m

theorem Map.toListInsert [auto ord: Ord k] (m: Map k v) (key: k) (value: v):
    Map.toList (Map.insert m key value) = Map.Spec.insert key value (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.insert m' key value) = Map.Spec.insert key value (Map.toList m')]
    (r => Map.Raw.toListInsert key value r) m

theorem Map.toListRemove [auto ord: Ord k] (m: Map k v) (key: k): Map.toList (Map.remove m key) = Map.Spec.remove key (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.remove m' key) = Map.Spec.remove key (Map.toList m')] (r => Map.Raw.toListRemove key r) m

theorem Map.toListAlter [auto ord: Ord k] (m: Map k v) (key: k) (f: Option v → Option v):
    Map.toList (Map.alter m key f) = Map.Spec.alter f key (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.alter m' key f) = Map.Spec.alter f key (Map.toList m')] (r => Map.Raw.toListAlter f key r) m

theorem Map.toListAdjust [auto ord: Ord k] (m: Map k v) (key: k) (f: v → v):
    Map.toList (Map.adjust m key f) = Map.Spec.adjust f key (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.adjust m' key f) = Map.Spec.adjust f key (Map.toList m')] (r => Map.Raw.toListAdjust f key r) m

theorem Map.toListMap (f: v → w) (m: Map k v [ord := o]): Map.toList (Map.map m f) = Map.Spec.mapValues f (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.map m' f) = Map.Spec.mapValues f (Map.toList m')] (r => Map.Raw.toListMap f r) m

theorem Map.toListFilter [auto ord: Ord k] (m: Map k v) (p: k → v → Bool): Map.toList (Map.filter m p) = Map.Spec.filter p (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.filter m' p) = Map.Spec.filter p (Map.toList m')] (r => Map.Raw.toListFilter p r) m

--| `filter` keeps the entries for which the test holds, in key order.
theorem Map.toListFilterList [auto ord: Ord k] (m: Map k v) (p: k → v → Bool):
    Map.toList (Map.filter m p) = List.filter (Map.toList m) (e => p e.fst e.snd) :=
  Map.indRaw [p := m' => Map.toList (Map.filter m' p) = List.filter (Map.toList m') (e => p e.fst e.snd)]
    (r => Map.Raw.toListFilterList r p) m

--| Filtering a map just to count it: the size of the filter is `count`.
theorem Map.sizeFilter [auto ord: Ord k] (m: Map k v) (p: k → v → Bool): Map.size (Map.filter m p) = Map.count m p :=
  Eq.trans (Map.sizeToList (Map.filter m p))
    (Eq.trans (Eq.cong List.length (Map.toListFilterList m p)) (List.lengthFilter (Map.toList m) (e => p e.fst e.snd)))

theorem Map.toListUnion [auto ord: Ord k] (a: Map k v) (b: Map k v):
    Map.toList (Map.union a b) = Map.Spec.union (Map.toList a) (Map.toList b) :=
  Map.indRaw [p := a' => Map.toList (Map.union a' b) = Map.Spec.union (Map.toList a') (Map.toList b)]
    (ra =>
      Map.indRaw [p := b' => Map.toList (Map.union (Map.ofRaw ra) b') = Map.Spec.union (Map.toList (Map.ofRaw ra)) (Map.toList b')]
        (rb => Map.Raw.toListUnion ra rb) b)
    a

theorem Map.foldLeftToList (f: b → k → v → b) (z: b) (m: Map k v [ord := o]):
    Map.foldLeft m z f = Map.Spec.foldLeft f z (Map.toList m) :=
  Map.indRaw [p := m' => Map.foldLeft m' z f = Map.Spec.foldLeft f z (Map.toList m')] (r => Map.Raw.foldLeftToList f z r) m

theorem Map.sizeToList (m: Map k v [ord := o]): Map.size m = List.length (Map.toList m) :=
  Map.indRaw [p := m' => Map.size m' = List.length (Map.toList m')] (r => Map.Raw.sizeToList r) m

--| A map has as many keys as entries.
theorem Map.lengthKeys (m: Map k v [ord := o]): List.length (Map.keys m) = Map.size m :=
  Eq.trans (List.lengthMap (Map.toList m) Pair.fst) (Eq.sym (Map.sizeToList m))

--| Inserting adds an entry unless the key is there already.
theorem Map.sizeInsert [auto ord: Ord k] (m: Map k v) (key: k) (value: v):
    Map.size (Map.insert m key value) = (if Map.contains m key then Map.size m else Map.size m + 1) :=
  rewrite Map.sizeToList (Map.insert m key value), Map.toListInsert m key value, Map.sizeToList m in
  match c: Map.get m key with
    | Some found =>
      Map.Spec.lengthInsertPresent key value found None (Map.toList m) (Map.toListSorted m) (Eq.trans (Eq.sym (Map.getToList m key)) c)
    | None =>
      Eq.trans (Map.Spec.lengthInsertAbsent key value (Map.toList m) (Eq.trans (Eq.sym (Map.getToList m key)) c))
        (Eq.sym (Nat.addOne (List.length (Map.toList m))))

--| Removing takes an entry away if the key is there.
theorem Map.sizeRemove [auto ord: Ord k] (m: Map k v) (key: k):
    Map.size (Map.remove m key) = (if Map.contains m key then Map.size m - 1 else Map.size m) :=
  rewrite Map.sizeToList (Map.remove m key), Map.toListRemove m key, Map.sizeToList m in
  match c: Map.get m key with
    | Some found =>
      Eq.cong (n => n - 1)
        (Map.Spec.lengthRemovePresent key found None (Map.toList m) (Map.toListSorted m) (Eq.trans (Eq.sym (Map.getToList m key)) c))
    | None => Eq.cong List.length (Map.Spec.removeAbsent key (Map.toList m) (Eq.trans (Eq.sym (Map.getToList m key)) c))

theorem Map.toListMapWithKey (f: k → v → w) (m: Map k v [ord := o]): Map.toList (Map.mapWithKey m f) = Map.Spec.mapWithKey f (Map.toList m) :=
  Map.indRaw [p := m' => Map.toList (Map.mapWithKey m' f) = Map.Spec.mapWithKey f (Map.toList m')] (r => Map.Raw.toListMapWithKey f r) m

theorem Map.minToList (m: Map k v [ord := o]): Map.min m = List.head (Map.toList m) :=
  Map.indRaw [p := m' => Map.min m' = List.head (Map.toList m')] (r => Map.Raw.minToList r) m

--| Views of two maps with the same entries left agree.
theorem Map.viewsAgree (x y: Option ((k, v), Map.Raw k v [ord := o]))
    (same: Option.map x (view => (view.fst, Map.Raw.toList view.snd)) = Option.map y (view => (view.fst, Map.Raw.toList view.snd))):
    Option.map x (view => (view.fst, Map.ofRaw view.snd)) = Option.map y (view => (view.fst, Map.ofRaw view.snd)) :=
  match x, y with
    | None, None => rfl
    | Some (smallest, rest), Some (other, otherRest) =>
      let pairs := Option.someInjective same
      rewrite Eq.cong Pair.fst pairs in
        Eq.cong (left => Some (other, left)) (Map.toListInjective (Map.ofRaw rest) (Map.ofRaw otherRest) (Eq.cong Pair.snd pairs))

theorem Map.popMinRespects (a: Map.Raw k v [ord := o]) (b: Map.Raw k v [ord := o]) (same: Map.Raw.Equiv a b): Map.popMinRaw a = Map.popMinRaw b :=
  Map.viewsAgree (Map.Raw.popMin a) (Map.Raw.popMin b)
    (Eq.trans (Map.Raw.popMinToList a) (Eq.trans (Eq.cong Map.Spec.uncons same) (Eq.sym (Map.Raw.popMinToList b))))

--| `popMinSpec` for one representative, given its view and its entries.
theorem Map.popMinSpecRaw [auto ord: Ord k] (r: Map.Raw k v)
    (x: Option ((k, v), Map.Raw k v)) (entries: List (k, v))
    (viewed: Option.map x (view => (view.fst, Map.Raw.toList view.snd)) = Map.Spec.uncons entries) (listed: Map.Raw.toList r = entries):
    Option.map x (view => (view.fst, Map.ofRaw view.snd)) = Option.map (List.head entries) (entry => (entry, Map.remove (Map.ofRaw r) entry.fst)) :=
  match x, entries with
    | None, [] => rfl
    | Some ((key, value), rest), [entry, ..more] =>
      let pairs := Option.someInjective viewed
      let first: (key, value) = entry := Eq.cong Pair.fst pairs
      let whole: Map.Raw.toList r = [(key, value), ..Map.Raw.toList rest] := rewrite first, Eq.cong Pair.snd pairs in listed
      let left: Map.Raw.toList rest = Map.Raw.toList (Map.Raw.remove key r) :=
        rewrite Map.Raw.toListRemove key r, whole, Ord.compareSelf key in rfl
      rewrite <- first in
        Eq.cong (later => Some ((key, value), later)) (Map.toListInjective (Map.ofRaw rest) (Map.ofRaw (Map.Raw.remove key r)) left)

--| `popMin` is `min` and `remove` together.
theorem Map.popMinSpec [auto ord: Ord k] (m: Map k v): Map.popMin m = Option.map (Map.min m) (entry => (entry, Map.remove m entry.fst)) :=
  Map.indRaw [p := m' => Map.popMin m' = Option.map (Map.min m') (entry => (entry, Map.remove m' entry.fst))]
    (r => rewrite Map.minToList (Map.ofRaw r) in Map.popMinSpecRaw r (Map.Raw.popMin r) (Map.Raw.toList r) (Map.Raw.popMinToList r) rfl) m

theorem Map.maxToList (m: Map k v [ord := o]): Map.max m = List.last (Map.toList m) :=
  Map.indRaw [p := m' => Map.max m' = List.last (Map.toList m')] (r => Map.Raw.maxToList r) m

theorem Map.belowToList [auto ord: Ord k] (m: Map k v) (key: k):
    Map.below m key = List.last (List.filter (Map.toList m) (e => Map.Spec.isLess e.fst key)) :=
  Map.indRaw [p := m' => Map.below m' key = List.last (List.filter (Map.toList m') (e => Map.Spec.isLess e.fst key))] (r => Map.Raw.belowToList r key) m

theorem Map.aboveToList [auto ord: Ord k] (m: Map k v) (key: k):
    Map.above m key = List.find (Map.toList m) (e => Map.Spec.isLess key e.fst) :=
  Map.indRaw [p := m' => Map.above m' key = List.find (Map.toList m') (e => Map.Spec.isLess key e.fst)] (r => Map.Raw.aboveToList r key) m

theorem Map.belowLastBelow [auto ord: Ord k] (m: Map k v) (key: k): Map.below m key = Map.Spec.lastBelow key None (Map.toList m) :=
  Eq.trans (Map.belowToList m key)
    (Eq.sym
      (Eq.trans (Map.Spec.lastBelowFilter key None (Map.toList m))
        (Map.Spec.lastOrNone (List.filter (Map.toList m) (e => Map.Spec.isLess e.fst key)))))

--| What `below` finds: an entry with a key below `key`, and no key of the
--| map between the two.
theorem Map.belowSome [auto ord: Ord k] (m: Map k v) (key: k) (found: k) (value: v) (h: Map.below m key = Some (found, value)):
    (Map.get m found = Some value) ∧ ((found < key) ∧ (∀ (other: k) => found < other → other < key → Map.contains m other = False)) :=
  let lastBelow: Map.Spec.lastBelow key None (Map.toList m) = Some (found, value) := Eq.trans (Eq.sym (Map.belowLastBelow m key)) h
  match Map.Spec.lastBelowFrom key None (Map.toList m) (found, value) lastBelow with
    | Inl none => Void.exfalso (Option.noneNotSome (found, value) none)
    | Inr (Both inList less) =>
      Both ((Map.memToList m found value).forward inList)
        (Both (ord.lessThanOf found key less)
          (other between beforeKey =>
            match has: Map.contains m other with
              | False => rfl
              | True =>
                Void.exfalso
                  (Map.Spec.lastBelowGreatest key None None (Map.toList m) (Map.toListSorted m) (found, value) lastBelow other
                    (Map.memKeysOfContains m other has) (ord.lessThanTo other key beforeKey) (ord.lessThanTo found other between))))

--| When `below` finds nothing, no key of the map is below `key`.
theorem Map.belowNone [auto ord: Ord k] (m: Map k v) (key: k) (h: Map.below m key = None) (other: k) (less: other < key):
    Map.contains m other = False :=
  match has: Map.contains m other with
    | False => rfl
    | True =>
      Void.exfalso
        (Map.Spec.lastBelowNone key None (Map.toList m) (Eq.trans (Eq.sym (Map.belowLastBelow m key)) h) other
          (Map.memKeysOfContains m other has) (ord.lessThanTo other key less))

--| What `above` finds: an entry with a key above `key`, and no key of the
--| map between the two.
theorem Map.aboveSome [auto ord: Ord k] (m: Map k v) (key: k) (found: k) (value: v) (h: Map.above m key = Some (found, value)):
    (Map.get m found = Some value) ∧ ((key < found) ∧ (∀ (other: k) => key < other → other < found → Map.contains m other = False)) :=
  let first: List.find (Map.toList m) (e => Map.Spec.isLess key e.fst) = Some (found, value) := Eq.trans (Eq.sym (Map.aboveToList m key)) h
  match List.findSome (Map.toList m) (e => Map.Spec.isLess key e.fst) (found, value) first with
    | Both passes inList =>
      Both ((Map.memToList m found value).forward inList)
        (Both (ord.lessThanOf key found (Map.Spec.isLessSound key found passes))
          (other afterKey beforeFound =>
            match has: Map.contains m other with
              | False => rfl
              | True =>
                Void.exfalso
                  (Map.Spec.findAboveLeast key None (Map.toList m) (Map.toListSorted m) (found, value) first other
                    (Map.memKeysOfContains m other has) (ord.lessThanTo key other afterKey) (ord.lessThanTo other found beforeFound))))

--| When `above` finds nothing, no key of the map is above `key`.
theorem Map.aboveNone [auto ord: Ord k] (m: Map k v) (key: k) (h: Map.above m key = None) (other: k) (more: key < other):
    Map.contains m other = False :=
  match got: Map.get m other with
    | None => rfl
    | Some value =>
      Void.exfalso
        (List.findNoneNotMem (Map.toList m) (e => Map.Spec.isLess key e.fst) (other, value) (Map.Spec.isLessOf key other (ord.lessThanTo key other more))
          ((Map.memToList m other value).backward got) (Eq.trans (Eq.sym (Map.aboveToList m key)) h))

-- What `get` says about each operation

theorem Map.getEmpty [auto ord: Ord k] (key: k): Map.get (Map.empty: Map k v) key = None := rfl

theorem Map.getInsert [auto ord: Ord k] (key: k) (value: v) (m: Map k v): (m |> Map.insert key value |> Map.get key) = Some value :=
  Map.indRaw [p := m' => (m' |> Map.insert key value |> Map.get key) = Some value] (r => Map.Raw.getInsert key value r) m

theorem Map.getInsertOther [auto ord: Ord k] (key: k) (value: v) (other: k) (ne: other ≠ key) (m: Map k v):
    (m |> Map.insert key value |> Map.get other) = Map.get m other :=
  Map.indRaw [p := m' => (m' |> Map.insert key value |> Map.get other) = Map.get m' other]
    (r => Map.Raw.getInsertOther key value other ne r) m

theorem Map.getInsertWith [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (f: v → v → v):
    Map.get (Map.insertWith m key value f) key = Some (Map.Tree.combine f value (Map.get m key)) :=
  Map.indRaw [p := m' => Map.get (Map.insertWith m' key value f) key = Some (Map.Tree.combine f value (Map.get m' key))]
    (r => Map.Raw.getInsertWith f key value r) m

theorem Map.getMap [auto ord: Ord k] (m: Map k v) (key: k) (f: v → w): Map.get (Map.map m f) key = Option.map (Map.get m key) f :=
  Map.indRaw [p := m' => Map.get (Map.map m' f) key = Option.map (Map.get m' key) f] (r => Map.Raw.getMap r key f) m

theorem Map.getFromList [auto ord: Ord k] (key: k) (xs: List (k, v)): Map.get (Map.fromList xs) key = Map.lookupLast key xs :=
  Map.Raw.getFromListFast key xs

--| The last pair for a key is in the second list, if it has one.
theorem Map.lookupLastAppendRight [auto ord: Ord k] (key: k) (ys: List (k, v)) [found: v] (got: Map.lookupLast key ys = Some found)
    (xs: List (k, v)): Map.lookupLast key (xs ++ ys) = Some found :=
  match xs with
    | [] => got
    | [(kk, vv), ..rest] => rewrite Map.lookupLastAppendRight key ys got rest in rfl

--| With no pair for the key in the second list, the last is the first list's.
theorem Map.lookupLastAppendLeft [auto ord: Ord k] (key: k) (ys: List (k, v)) (missing: Map.lookupLast key ys = None)
    (xs: List (k, v)): Map.lookupLast key (xs ++ ys) = Map.lookupLast key xs :=
  match xs with
    | [] => missing
    | [(kk, vv), ..rest] => rewrite Map.lookupLastAppendLeft key ys missing rest in rfl

--| A first pair with another key doesn't change the last pair for `key`.
theorem Map.lookupLastConsOther [auto ord: Ord k] (key: k) (kk: k) (vv: v) (rest: List (k, v)) (apart: key ≠ kk):
    Map.lookupLast key [(kk, vv), ..rest] = Map.lookupLast key rest :=
  match found: Map.lookupLast key rest with
    | Some x => rfl
    | None =>
      match e: Ord.compare key kk with
        | Equal => Void.exfalso (apart (ord.equal key kk e))
        | Less => rfl
        | Greater => rfl

--| A first pair for `key` is the last one when the rest has none.
theorem Map.lookupLastConsSame [auto ord: Ord k] (key: k) (vv: v) (rest: List (k, v)) (missing: Map.lookupLast key rest = None):
    Map.lookupLast key [(key, vv), ..rest] = Some vv :=
  rewrite missing, Ord.compareSelf key in rfl

--| In a map's own list each key appears once, so the last pair for a key is
--| what `get` finds.
theorem Map.lookupLastToList [auto ord: Ord k] (m: Map k v) (key: k): Map.lookupLast key (Map.toList m) = Map.get m key :=
  Eq.trans (Map.Spec.lookupLastAscending key None (Map.toList m) (Map.toListSorted m)) (Eq.sym (Map.getToList m key))

theorem Map.getInsertWithOther [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (other: k) (ne: other ≠ key) (f: v → v → v):
    Map.get (Map.insertWith m key value f) other = Map.get m other :=
  Map.indRaw [p := m' => Map.get (Map.insertWith m' key value f) other = Map.get m' other] (r => Map.Raw.getInsertWithOther f key value other ne r) m

--| What a map holds after an insert: the new entry, or what it held before.
theorem Map.getInsertCases [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (other: k) (found: v)
    (there: Map.get (Map.insert m key value) other = Some found): ((other = key) ∧ (found = value)) ∨ (Map.get m other = Some found) :=
  match same: other == key with
    | True =>
      let equal := same.read
      Inl (Both equal (Option.someInjective (Eq.trans (Eq.sym there) (rewrite equal in Map.getInsert key value m))))
    | False => Inr (Eq.trans (Eq.sym (Map.getInsertOther key value other same.read m)) there)

--| Inserting a key not there keeps every entry.
theorem Map.getInsertKeeps [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (fresh: Map.contains m key = False) (other: k) (found: v)
    (there: Map.get m other = Some found): Map.get (Map.insert m key value) other = Some found :=
  match same: other == key with
    | True =>
      let equal := same.read
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym fresh) (rewrite <- equal in Map.containsOfGet m other found there)))
    | False => Eq.trans (Map.getInsertOther key value other same.read m) there

--| Reading after an insert gives the new value at the key and what was there
--| elsewhere.
theorem Map.getOrInsert [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (other: k) (fallback: v):
    (m.insert key value).getOr other fallback = (if key == other then value else m.getOr other fallback) :=
  match same: key == other with
    | True => rewrite <- same.read in (rewrite Map.getInsert key value m in rfl)
    | False =>
      let apart: other ≠ key := isSame => Bool.trueNotFalse (rewrite isSame, DecEq.refl key at same in same)
      rewrite Map.getInsertOther key value other apart m in rfl

--| Inserting one value at each of several keys: reading a key among them
--| gives the value, any other key gives what the map held.
theorem Map.getOrInsertAll [auto ord: Ord k] (value: v) (other: k) (fallback: v) (keys: List k) (m: Map k v): (keys.foldLeft m (written key => written.insert key value)).getOr other fallback
    = (if keys.contains other then value else m.getOr other fallback) :=
  match keys with
    | [] => rfl
    | [key, ..rest] =>
      rewrite Map.getOrInsertAll value other fallback rest (m.insert key value), Map.getOrInsert m key value other fallback in cases

--| The values add up to the same as `f` over the keys, when `f` reads the map
--| (with 0 for a key not in it): the way to sum a map's values with a spec
--| function over its keys.
theorem Map.sumValuesEqSumByKeys [auto ord: Ord k] (m: Map k Nat) (f: k → Nat) (reads: ∀ (key: k) => f key = m.getOr key 0):
    m.values.sum = m.keys.sumBy f :=
  calc m.values.sum
    _ = m.toList.sumBy Pair.snd := List.foldLeftMap m.toList 0 Nat.add Pair.snd
    _ = m.toList.sumBy (entry => f entry.fst) :=
      List.sumByCongMem m.toList Pair.snd (entry => f entry.fst)
        (((key, value)) member =>
          Eq.sym (Eq.trans (reads key) (rewrite (Map.memToList m key value).forward member in rfl)))
    _ = m.keys.sumBy f := Eq.sym (List.foldLeftMap m.toList 0 (total key => total + f key) Pair.fst)

--| A key `contains` finds has a value.
theorem Map.getOfContains [auto ord: Ord k] (m: Map k v) (key: k) (there: Map.contains m key = True): Exists v (value => Map.get m key = Some value) :=
  match found: Map.get m key with
    | Some value => Witness value rfl

--| A key just inserted is there.
theorem Map.containsInsertSame [auto ord: Ord k] (m: Map k v) (key: k) (value: v): Map.contains (Map.insert m key value) key = True :=
  rewrite Map.getInsert key value m in rfl

--| Inserting keeps the keys already there.
theorem Map.containsInsertKeeps [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (other: k) (there: Map.contains m other = True):
    Map.contains (Map.insert m key value) other = True :=
  match same: other == key with
    | True => rewrite same.read in Map.containsInsertSame m key value
    | False => rewrite Map.getInsertOther key value other same.read m in there

theorem Map.getRemove [auto ord: Ord k] (m: Map k v) (key: k): Map.get (Map.remove m key) key = None :=
  Map.indRaw [p := m' => Map.get (Map.remove m' key) key = None] (r => Map.Raw.getRemove key r) m

theorem Map.getRemoveOther [auto ord: Ord k] (m: Map k v) (key: k) (other: k) (ne: other ≠ key):
    Map.get (Map.remove m key) other = Map.get m other :=
  Map.indRaw [p := m' => Map.get (Map.remove m' key) other = Map.get m' other] (r => Map.Raw.getRemoveOther key other ne r) m

theorem Map.getAlter [auto ord: Ord k] (m: Map k v) (key: k) (f: Option v → Option v): Map.get (Map.alter m key f) key = f (Map.get m key) :=
  Map.indRaw [p := m' => Map.get (Map.alter m' key f) key = f (Map.get m' key)] (r => Map.Raw.getAlter f key r) m

theorem Map.getAlterOther [auto ord: Ord k] (m: Map k v) (key: k) (other: k) (ne: other ≠ key) (f: Option v → Option v):
    Map.get (Map.alter m key f) other = Map.get m other :=
  Map.indRaw [p := m' => Map.get (Map.alter m' key f) other = Map.get m' other] (r => Map.Raw.getAlterOther f key other ne r) m

theorem Map.getAdjust [auto ord: Ord k] (m: Map k v) (key: k) (f: v → v): Map.get (Map.adjust m key f) key = Option.map (Map.get m key) f :=
  Map.indRaw [p := m' => Map.get (Map.adjust m' key f) key = Option.map (Map.get m' key) f] (r => Map.Raw.getAdjust r key f) m

theorem Map.getAdjustOther [auto ord: Ord k] (m: Map k v) (key: k) (other: k) (ne: other ≠ key) (f: v → v):
    Map.get (Map.adjust m key f) other = Map.get m other :=
  Map.indRaw [p := m' => Map.get (Map.adjust m' key f) other = Map.get m' other] (r => Map.Raw.getAdjustOther f key other ne r) m

--| `filter` keeps the value at `key` if `p` holds of it.
theorem Map.getFilter [auto ord: Ord k] (m: Map k v) (key: k) (p: k → v → Bool):
    Map.get (Map.filter m p) key = Option.filter (Map.get m key) (p key) :=
  Eq.trans (Map.getToList (Map.filter m p) key)
    (Eq.trans (Eq.cong (Map.Tree.lookupList key) (Map.toListFilterList m p))
      (Eq.trans (Map.Spec.lookupFilter p key None (Map.toList m) (Map.toListSorted m))
        (Eq.cong (.filter (p key)) (Eq.sym (Map.getToList m key)))))

--| A key is in a filtered map exactly when it is in the map with a value `p`
--| keeps.
theorem Map.containsFilter [auto ord: Ord k] (m: Map k v) (key: k) (p: k → v → Bool):
    Map.contains (Map.filter m p) key = Option.any (Map.get m key) (p key) :=
  rewrite Map.getFilter m key p in
    match Map.get m key with
      | Some value => match p key value with
        | True => rfl
        | False => rfl
      | None => rfl

--| What a fold over sorted entries leaves at `key`, for a step that changes
--| only the key it's given (`atKey`, `elsewhere`), such as inserting each
--| entry in turn. A sorted list has at most one entry at `key`.
theorem Map.getFold [auto ord: Ord k] (step: Map k w → k → v → Map k w) (h: v → Option w → Option w) (key: k)
    (atKey: ∀ (m: Map k w) (value: v) => Map.get (step m key value) key = h value (Map.get m key))
    (elsewhere: ∀ (m: Map k w) (kk: k) (value: v) => key ≠ kk → Map.get (step m kk value) key = Map.get m key)
    (lo: Option k) (xs: List (k, v)) (m: Map k w) (asc: Map.Spec.Ascending ord lo xs):
    Map.get (Map.Spec.foldLeft step m xs) key = Map.Spec.atKey h (Map.Tree.lookupList key xs) (Map.get m key) :=
  match xs, asc with
    | [], asc => rfl
    | [(kk, vv), ..rest], Both a arest =>
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

--| `unionWith`: the values there are, with `f` where both maps have one.
theorem Map.getUnionWith [auto ord: Ord k] (a: Map k v) (key: k) (b: Map k v) (f: v → v → v):
    Map.get (Map.unionWith a b f) key = Option.merge (Map.get a key) (Map.get b key) f :=
  Map.indRaw [p := a' => Map.get (Map.unionWith a' b f) key = Option.merge (Map.get a' key) (Map.get b key) f]
    (ra =>
      Map.indRaw [p := b' => Map.get (Map.unionWith (Map.ofRaw ra) b' f) key = Option.merge (Map.get (Map.ofRaw ra) key) (Map.get b' key) f]
        (rb => Map.Raw.getUnionWith ra key rb f) b)
    a

--| Merging that keeps the first value is `orElse`.
theorem Map.Spec.mergeFirst (a b: Option v): Option.merge a b (x y => x) = Option.orElse a b :=
  match a, b with
    | Some x, Some y => rfl
    | Some x, None => rfl
    | None, Some y => rfl
    | None, None => rfl

--| Inserting into a raw map, then taking its class, is inserting into the class.
theorem Map.ofRawFoldInsert [auto ord: Ord k] (xs: List (k, v)) (r: Map.Raw k v): Map.ofRaw (Map.Spec.foldLeft (acc key value => Map.Raw.insert key value acc) r xs)
    = Map.Spec.foldLeft (acc key value => Map.insert acc key value) (Map.ofRaw r) xs :=
  match xs with
    | [] => rfl
    | [(kk, vv), ..rest] => Map.ofRawFoldInsert rest (Map.Raw.insert kk vv r)

theorem Map.getUnionRaw [auto ord: Ord k] (key: k) (ra: Map.Raw k v) (rb: Map.Raw k v):
    Map.get (Map.union (Map.ofRaw ra) (Map.ofRaw rb)) key = Option.orElse (Map.Raw.get key ra) (Map.Raw.get key rb) :=
  Eq.trans (Map.Raw.getUnionWith ra key rb (new old => new)) (Map.Spec.mergeFirst (Map.Raw.get key ra) (Map.Raw.get key rb))

--| `union`: the first map's value, else the second's.
theorem Map.getUnion [auto ord: Ord k] (a: Map k v) (key: k) (b: Map k v):
    Map.get (Map.union a b) key = Option.orElse (Map.get a key) (Map.get b key) :=
  Map.indRaw [p := a' => Map.get (Map.union a' b) key = Option.orElse (Map.get a' key) (Map.get b key)]
    (ra =>
      Map.indRaw [p := b' => Map.get (Map.union (Map.ofRaw ra) b') key = Option.orElse (Map.get (Map.ofRaw ra) key) (Map.get b' key)]
        (rb => Map.getUnionRaw key ra rb) b)
    a

--| What `Map.fromListWith xs f` keeps at `key`: each value with the key in turn,
--| combined by `f new old` with what was found before.
@[tailrec]
def Map.lookupWithOnto [auto ord: Ord k] (f: v → v → v) (key: k): (found: Option v) → (entries: List (k, v)) → Option v
  | found, [] => found
  | found, [(kk, vv), ..rest] => match Ord.compare key kk with
    | Equal => Map.lookupWithOnto f key (Some (Map.Tree.combine f vv found)) rest
    | _ => Map.lookupWithOnto f key found rest

--| What `Map.fromListWith xs f` holds at `key`: its values in `xs` combined by `f new old`, if there are any.
def Map.lookupWith [auto ord: Ord k] (f: v → v → v) (key: k) (xs: List (k, v)): Option v := Map.lookupWithOnto f key None xs

theorem Map.getFoldInsertWith [auto ord: Ord k] (m: Map k v) (key: k) (xs: List (k, v)) (f: v → v → v):
    Map.get (List.foldLeft xs m (acc entry => Map.insertWith acc entry.fst entry.snd f)) key = Map.lookupWithOnto f key (Map.get m key) xs :=
  match xs with
    | [] => rfl
    | [(kk, vv), ..rest] =>
      rewrite Map.getFoldInsertWith (Map.insertWith m kk vv f) key rest f in
      match e: Ord.compare key kk with
        | Less => rewrite Map.getInsertWithOther m kk vv key (Map.Spec.notEqualOfCompare key kk (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) f in rfl
        | Equal => rewrite ord.equal key kk e, Map.getInsertWith m kk vv f in rfl
        | Greater => rewrite Map.getInsertWithOther m kk vv key (Map.Spec.notEqualOfCompare key kk (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) f in rfl

theorem Map.getFromListWith [auto ord: Ord k] (xs: List (k, v)) (key: k) (f: v → v → v):
    Map.get (Map.fromListWith xs f) key = Map.lookupWith f key xs :=
  Map.getFoldInsertWith Map.empty key xs f

theorem Map.getOrCountStep [auto ord: Ord k] (m: Map k Nat) (key: k) (x: k):
    Map.getOr (Map.insertWith m x 1 Nat.add) key 0 = Nat.succIf (Map.getOr m key 0) (Map.Spec.sameKey key x) :=
  match e: Ord.compare key x with
    | Equal =>
      rewrite ord.equal key x e, Map.getInsertWith m x 1 Nat.add in
      match c: Map.get m x with
        | None => rfl
        | Some n => rfl
    | Less => rewrite Map.getInsertWithOther m x 1 key (Map.Spec.notEqualOfCompare key x (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) Nat.add in rfl
    | Greater => rewrite Map.getInsertWithOther m x 1 key (Map.Spec.notEqualOfCompare key x (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) Nat.add in rfl

theorem Map.getOrFoldCount [auto ord: Ord k] (m: Map k Nat) (key: k) (xs: List k): Map.getOr (List.foldLeft xs m (acc x => Map.insertWith acc x 1 Nat.add)) key 0
    = List.foldLeft xs (Map.getOr m key 0) (n x => Nat.succIf n (Map.Spec.sameKey key x)) :=
  match xs with
    | [] => rfl
    | [x, ..rest] =>
      Eq.trans (Map.getOrFoldCount (Map.insertWith m x 1 Nat.add) key rest)
        (Eq.cong (n => List.foldLeft rest n (n2 y => Nat.succIf n2 (Map.Spec.sameKey key y))) (Map.getOrCountStep m key x))

--| `counts`: how many elements equal `key`.
theorem Map.getOrCounts [auto ord: Ord k] (key: k) (xs: List k): (Map.counts xs).getOr key 0 = xs.count (== key) :=
  Eq.trans (Map.getOrFoldCount Map.empty key xs)
    (List.countCongMem _ (x => Map.Spec.sameKey key x) (== key) (x m => Map.Spec.sameKeyDecide key x))

theorem Map.countsFoldPositive [auto ord: Ord k]: ∀ (xs: List k) (m: Map k Nat) (key: k) => (∀ (n: Nat) => Map.get m key = Some n → 0 < n) →
    ∀ (n: Nat) => Map.get (List.foldLeft xs m (acc x => Map.insertWith acc x 1 Nat.add)) key = Some n → 0 < n
  | [], m, key, h, n, found => h n found
  | [x, ..rest], m, key, h, n, found =>
    Map.countsFoldPositive rest (Map.insertWith m x 1 Nat.add) key
      (n g =>
        match e: Ord.compare key x with
          | Equal =>
            let inserted := rewrite ord.equal key x e, Map.getInsertWith m x 1 Nat.add at g
            match c: Map.get m x with
              | None => rewrite <- Option.someInjective inserted in rfl
              | Some old => rewrite <- Option.someInjective inserted in rfl
          | Less =>
            h n (rewrite Map.getInsertWithOther m x 1 key (Map.Spec.notEqualOfCompare key x (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) Nat.add at g)
          | Greater =>
            h n (rewrite Map.getInsertWithOther m x 1 key (Map.Spec.notEqualOfCompare key x (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) Nat.add at g))
      n found

--| `counts` records no count of 0: each key it has is in the list.
theorem Map.countsPositive [auto ord: Ord k] (xs: List k) (key: k) (n: Nat) (found: Map.get (Map.counts xs) key = Some n): 0 < n :=
  Map.countsFoldPositive xs Map.empty key (n g => Void.exfalso (Option.noneNotSome n g)) n found

--| Weighing a map of counts: each count times `f` of its key, added up. Adding
--| `n` at `key` with `Nat.add` adds `n * f key`, whether the key is new or
--| already there.
theorem Map.specInsertWithWeight [auto ord: Ord k] (f: k → Nat) (key: k) (n: Nat)
    (entries: List (k, Nat)):
    List.sumBy (Map.Spec.insertWith Nat.add key n entries) (entry => entry.snd * f entry.fst) = n * f key + List.sumBy entries (entry => entry.snd * f entry.fst) :=
  match entries with
    | [] => omega [List.sumByCons [] (key, n) (entry => entry.snd * f entry.fst)]
    | [(kk, vv), ..rest] =>
      match e: Ord.compare key kk with
        | Less => omega [List.sumByCons [(kk, vv), ..rest] (key, n) (entry => entry.snd * f entry.fst)]
        | Equal =>
          let same := ord.equal key kk e
          let spread: (n + vv) * f kk = n * f kk + vv * f kk := ring
          rewrite same in
            omega [List.sumByCons rest (kk, n + vv) (entry => entry.snd * f entry.fst), List.sumByCons rest (kk, vv) (entry => entry.snd * f entry.fst), spread]
        | Greater =>
          omega [
            List.sumByCons (Map.Spec.insertWith Nat.add key n rest) (kk, vv) (entry => entry.snd * f entry.fst),
            List.sumByCons rest (kk, vv) (entry => entry.snd * f entry.fst),
            Map.specInsertWithWeight f key n rest
          ]

--| The `insertWith` step: the weight of a map of counts, after adding `n` at
--| `key`, is `n * f key` more.
theorem Map.weightInsertWith [auto ord: Ord k] (m: Map k Nat) (key: k) (n: Nat) (f: k → Nat):
    List.sumBy (Map.toList (Map.insertWith m key n Nat.add)) (entry => entry.snd * f entry.fst)
      = n * f key + List.sumBy (Map.toList m) (entry => entry.snd * f entry.fst) :=
  rewrite Map.toListInsertWith m key n Nat.add in Map.specInsertWithWeight f key n (Map.toList m)

theorem Map.countsFoldWeight [auto ord: Ord k] (f: k → Nat) (xs: List k) (m: Map k Nat): List.sumBy (Map.toList (List.foldLeft xs m (acc x => Map.insertWith acc x 1 Nat.add))) (entry => entry.snd * f entry.fst)
    = List.sumBy xs f + List.sumBy (Map.toList m) (entry => entry.snd * f entry.fst) :=
  match xs with
    | [] => omega
    | [x, ..rest] =>
      rewrite Map.countsFoldWeight f rest (Map.insertWith m x 1 Nat.add), Map.weightInsertWith m x 1 f, List.sumByCons rest x f in ring

--| Weighing `Map.counts xs` by `f` is summing `f` over `xs`: each count times
--| `f` of its key, added up, equals `xs.sumBy f`.
theorem Map.sumByCounts [auto ord: Ord k] (xs: List k) (f: k → Nat):
    List.sumBy (Map.toList (Map.counts xs)) (entry => entry.snd * f entry.fst) = List.sumBy xs f :=
  Eq.trans (Map.countsFoldWeight f xs Map.empty) (omega)

--| `groupBy`: the elements whose key is `kk`, in list order, if there are any.
theorem Map.getGroupBy [auto ord: Ord k] (key: a → k) (kk: k) (xs: List a):
    Map.get (Map.groupBy xs key) kk = List.nonEmpty (List.filter xs (x => Map.Spec.sameKey kk (key x))) :=
  match xs with
    | [] => rfl
    | [x, ..rest] =>
      rewrite List.foldRightCons rest x Map.empty (x m => Map.insertWith m (key x) (NonEmptyList.singleton x) NonEmptyList.append) in
      match e: Ord.compare kk (key x) with
        | Equal =>
          rewrite ord.equal kk (key x) e, Map.getInsertWith (Map.groupBy rest key) (key x) (NonEmptyList.singleton x) NonEmptyList.append, Map.getGroupBy key (key x) rest in
          match c: List.filter rest (y => Map.Spec.sameKey (key x) (key y)) with
            | [] => rfl
            | [y, ..ys] => rfl
        | Less =>
          rewrite Map.getInsertWithOther (Map.groupBy rest key) (key x) (NonEmptyList.singleton x) kk
            (Map.Spec.notEqualOfCompare kk (key x) (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) NonEmptyList.append in
          Map.getGroupBy key kk rest
        | Greater =>
          rewrite Map.getInsertWithOther (Map.groupBy rest key) (key x) (NonEmptyList.singleton x) kk
            (Map.Spec.notEqualOfCompare kk (key x) (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) NonEmptyList.append in
          Map.getGroupBy key kk rest

--| `groupMap`: the values of the elements whose key is `kk`, in list order, if
--| there are any ([`Map.groupMap`], [`Map.groupBy`]).
theorem Map.getGroupMap [auto ord: Ord k] (key: a → k) (value: a → v) (kk: k) (xs: List a):
    Map.get (Map.groupMap xs key value) kk = List.nonEmpty (List.map (List.filter xs (x => Map.Spec.sameKey kk (key x))) value) :=
  match xs with
    | [] => rfl
    | [x, ..rest] =>
      rewrite List.foldRightCons rest x Map.empty (x m => Map.insertWith m (key x) (NonEmptyList.singleton (value x)) NonEmptyList.append) in
      match e: Ord.compare kk (key x) with
        | Equal =>
          rewrite ord.equal kk (key x) e, Map.getInsertWith (Map.groupMap rest key value) (key x) (NonEmptyList.singleton (value x)) NonEmptyList.append, Map.getGroupMap key value (key x) rest in
          match c: List.filter rest (y => Map.Spec.sameKey (key x) (key y)) with
            | [] => rfl
            | [y, ..ys] => rfl
        | Less =>
          rewrite Map.getInsertWithOther (Map.groupMap rest key value) (key x) (NonEmptyList.singleton (value x)) kk
            (Map.Spec.notEqualOfCompare kk (key x) (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) NonEmptyList.append in
          Map.getGroupMap key value kk rest
        | Greater =>
          rewrite Map.getInsertWithOther (Map.groupMap rest key value) (key x) (NonEmptyList.singleton (value x)) kk
            (Map.Spec.notEqualOfCompare kk (key x) (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) NonEmptyList.append in
          Map.getGroupMap key value kk rest

theorem Map.orElseNone (o: Option a): Option.orElse o None = o :=
  match o with
    | None => rfl
    | Some x => rfl

--| `indexBy` from a starting map: what the map has, else the first element
--| whose key is `kk`.
theorem Map.getIndexByFrom [auto ord: Ord k] (key: a → k) (kk: k) (xs: List a) (m: Map k a): Map.get (List.foldLeft xs m (index element => Map.insertWith index (key element) element (newer older => older))) kk
    = Option.orElse (Map.get m kk) (List.find xs (x => Map.Spec.sameKey kk (key x))) :=
  match xs with
    | [] => Eq.sym (Map.orElseNone (Map.get m kk))
    | [x, ..rest] =>
      match e: Ord.compare kk (key x) with
        | Equal =>
          rewrite ord.equal kk (key x) e in
          Eq.trans (Map.getIndexByFrom key (key x) rest (Map.insertWith m (key x) x (newer older => older)))
            (Eq.trans (Eq.cong (o => Option.orElse o (List.find rest (y => Map.Spec.sameKey (key x) (key y)))) (Map.getInsertWith m (key x) x (newer older => older)))
              (match c: Map.get m (key x) with
                | None => rfl
                | Some o => rfl))
        | Less =>
          Eq.trans (Map.getIndexByFrom key kk rest (Map.insertWith m (key x) x (newer older => older)))
            (Eq.cong (o => Option.orElse o (List.find rest (y => Map.Spec.sameKey kk (key y))))
              (Map.getInsertWithOther m (key x) x kk
                (Map.Spec.notEqualOfCompare kk (key x) (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) (newer older => older)))
        | Greater =>
          Eq.trans (Map.getIndexByFrom key kk rest (Map.insertWith m (key x) x (newer older => older)))
            (Eq.cong (o => Option.orElse o (List.find rest (y => Map.Spec.sameKey kk (key y))))
              (Map.getInsertWithOther m (key x) x kk
                (Map.Spec.notEqualOfCompare kk (key x) (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) (newer older => older)))

--| `indexBy`: the first element whose key is `kk`.
theorem Map.getIndexBy [auto ord: Ord k] (key: a → k) (kk: k) (xs: List a):
    Map.get (Map.indexBy xs key) kk = List.find xs (x => Map.Spec.sameKey kk (key x)) :=
  Map.getIndexByFrom key kk xs Map.empty

--| What `indexBy` has under a key is the first element with that key, found with `==`, as a program finding by key writes it.
theorem Map.getIndexByEq [auto ord: Ord k] (xs: List a) (kk: k) (key: a → k):
    Map.get (Map.indexBy xs key) kk = List.find xs (x => key x == kk) :=
  Eq.trans (Map.getIndexBy key kk xs) (List.findCong xs (x => Map.Spec.sameKey kk (key x)) (x => key x == kk) (x => Map.Spec.sameKeyDecide kk (key x)))

--| What `indexBy` has under `kk` has key `kk`.
theorem Map.indexByKey [auto ord: Ord k] (xs: List a) (kk: k) (key: a → k) (y: a) (h: Map.get (Map.indexBy xs key) kk = Some y): key y = kk :=
  match List.findSome xs (x => Map.Spec.sameKey kk (key x)) y (Eq.trans (Eq.sym (Map.getIndexBy key kk xs)) h) with
    | Both py m => Eq.sym (Map.Spec.sameKeySound kk (key y) py)

--| What `indexBy` has under a text key is the first element with that key by `Text`'s own `==`.
theorem Map.getIndexByText (xs: List a) (kk: Text) (key: a → Text): Map.get (Map.indexBy xs key) kk = List.find xs (x => key x == kk) :=
  Map.getIndexByEq xs kk key

--| With distinct keys, `indexBy` has each element under its own key.
theorem Map.getIndexByMem [auto ord: Ord k] (xs: List a) (key: a → k) (d: List.Distinct (List.map xs key)) (x: a) (m: List.Mem x xs):
    Map.get (Map.indexBy xs key) (key x) = Some x :=
  Eq.trans (Map.getIndexByEq xs (key x) key) (List.findKeyDistinct key xs d x m)

--| `indexBy` has a key exactly when some element has it: its keys are the
--| elements' keys.
theorem Map.containsIndexBy [auto ord: Ord k] (xs: List a) (key: a → k) (kk: k):
    Map.contains (Map.indexBy xs key) kk = List.any xs (x => key x == kk) :=
  rewrite Map.getIndexByEq xs kk key, List.anyFind (x => key x == kk) xs in
  match c: List.find xs (x => key x == kk) with
    | Some y => rfl
    | None => rfl

theorem Map.memKeysIndexBy [auto ord: Ord k] (xs: List a) (key: a → k) (kk: k):
    List.Mem kk (Map.keys (Map.indexBy xs key)) ↔ List.Mem kk (List.map xs key) := {
  forward = inKeys =>
    let found: xs.any (x => key x == kk) := Eq.trans (Eq.sym (Map.containsIndexBy xs key kk)) ((Map.memKeys (Map.indexBy xs key) kk).forward inKeys)
    let Witness x (Both inXs e) := found
    rewrite <- e.read in List.memMap xs x inXs key,
  backward = inMap =>
    (Map.memKeys (Map.indexBy xs key) kk).backward
      (Eq.trans (Map.containsIndexBy xs key kk)
        (List.anyElim (x => key x = kk) (List.any xs (x => key x == kk) = True) xs (List.memMapAny xs key kk inMap)
          (x inXs e => Witness x (Both inXs (rewrite e in DecEq.refl kk)))))
}

theorem Map.getIndexByMemExample: Map.get (Map.indexBy ["ab", "c"] Text.length) 2 = Some "ab" := rfl

--| Whatever the keys, what `indexBy` has under `kk` is an element of the
--| list with key `kk`.
theorem Map.memOfGetIndexBy [auto ord: Ord k] (xs: List a) (key: a → k) (kk: k) (y: a) (h: Map.get (Map.indexBy xs key) kk = Some y):
    y ∈ xs ∧ key y = kk :=
  match List.findSome xs (x => Map.Spec.sameKey kk (key x)) y (Eq.trans (Eq.sym (Map.getIndexBy key kk xs)) h) with
    | Both py m => Both m (Eq.sym (Map.Spec.sameKeySound kk (key y) py))

--| `indexBy` has every element's key, with an element that has that key under it.
--| That is the first such element ([`Map.getIndexByEq`]), and with distinct
--| keys the element itself ([`Map.getIndexByMem`]).
theorem Map.getIndexByOfMem [auto ord: Ord k] (xs: List a) (key: a → k) (x: a) (m: x ∈ xs):
    ∃ (y: a) => Map.get (Map.indexBy xs key) (key x) = Some y ∧ y ∈ xs ∧ key y = key x :=
  match c: Map.get (Map.indexBy xs key) (key x) with
    | Some y => Witness y (Both rfl (Map.memOfGetIndexBy xs key (key x) y c))
    | None =>
      Void.exfalso (List.findKeySome xs key (key x) (List.memMap xs x m key) (Eq.trans (Eq.sym (Map.getIndexByEq xs (key x) key)) c))

--| Indexing words by length, any word's length finds a word of that length.
theorem Map.getIndexByOfMemExample (words: List Text) (word: Text) (m: word ∈ words):
    ∃ (y: Text) => Map.get (Map.indexBy words Text.length) (Text.length word) = Some y ∧ y ∈ words ∧ Text.length y = Text.length word :=
  Map.getIndexByOfMem words Text.length word m

theorem Map.getMapWithKey [auto ord: Ord k] (m: Map k v) (key: k) (f: k → v → w):
    Map.get (Map.mapWithKey m f) key = Option.map (Map.get m key) (f key) :=
  Map.indRaw [p := m' => Map.get (Map.mapWithKey m' f) key = Option.map (Map.get m' key) (f key)] (r => Map.Raw.getMapWithKey r key f) m

--| `filterMap`: `f` of the value at `key`, if there is one.
theorem Map.getFilterMap [auto ord: Ord k] (m: Map k v) (key: k) (f: k → v → Option w):
    Map.get (Map.filterMap m f) key = Option.flatMap (Map.get m key) (f key) :=
  Map.indRaw [p := m' => Map.get (Map.filterMap m' f) key = Option.flatMap (Map.get m' key) (f key)] (r => Map.Raw.getMapMaybe r key f) m

theorem Map.getIntersectWith [auto ord: Ord k] (a: Map k v) (key: k) (b: Map k w) (f: v → w → x):
    Map.get (Map.intersectWith a b f) key = Option.flatMap (Map.get a key) (value => Option.map (Map.get b key) (f value)) :=
  Map.indRaw [p := a' => Map.get (Map.intersectWith a' b f) key = Option.flatMap (Map.get a' key) (value => Option.map (Map.get b key) (f value))]
    (ra =>
      Map.indRaw
        [p := b' => Map.get (Map.intersectWith (Map.ofRaw ra) b' f) key
          = Option.flatMap (Map.get (Map.ofRaw ra) key) (value => Option.map (Map.get b' key) (f value))]
        (rb => Map.Raw.getIntersectWith ra key rb f) b)
    a

theorem Map.getDifference [auto ord: Ord k] (a: Map k v) (key: k) (b: Map k w):
    Map.get (Map.difference a b) key = Option.filter (Map.get a key) (value => ¬(Map.contains b key)) :=
  Map.indRaw [p := a' => Map.get (Map.difference a' b) key = Option.filter (Map.get a' key) (value => ¬(Map.contains b key))]
    (ra =>
      Map.indRaw
        [p := b' => Map.get (Map.difference (Map.ofRaw ra) b') key = Option.filter (Map.get (Map.ofRaw ra) key) (value => ¬(Map.contains b' key))]
        (rb => Map.Raw.getDifference ra key rb) b)
    a

--| `range`: the value at `key` if `lo <= key < hi`.
theorem Map.getRange [auto ord: Ord k] (m: Map k v) (lo: k) (hi: k) (key: k):
    Map.get (Map.range m lo hi) key = (if ¬(Map.Spec.isLess key lo) ∧ Map.Spec.isLess key hi then Map.get m key else None) :=
  rewrite Map.getFilter m key (key2 value => ¬(Map.Spec.isLess key2 lo) ∧ Map.Spec.isLess key2 hi) in
  match c: ¬(Map.Spec.isLess key lo) ∧ Map.Spec.isLess key hi with
    | True =>
      match d: Map.get m key with
        | None => rfl
        | Some value => rfl
    | False =>
      match d: Map.get m key with
        | None => rfl
        | Some value => rfl

--| `mapKeys`: the last entry, in key order, whose new key is `key`.
theorem Map.getMapKeys [auto ord: Ord j] (f: k → j) (key: j) (m: Map k v [ord := o]):
    Map.get (Map.mapKeys m f) key = Map.lookupLast key (List.map (Map.toList m) (e => (f e.fst, e.snd))) :=
  Map.getFromList key (List.map (Map.toList m) (e => (f e.fst, e.snd)))

-- Equations between maps

--| Inserting two different keys in either order gives the same map.
theorem Map.insertComm [auto ord: Ord k] (a: k) (x: v) (b: k) (y: v) (ne: a ≠ b) (m: Map k v):
    (m |> Map.insert a x |> Map.insert b y) = (m |> Map.insert b y |> Map.insert a x) :=
  Map.ext ((m.insert a x).insert b y) ((m.insert b y).insert a x) (key =>
    if hb: key = b then
      rewrite hb in
      Eq.trans (Map.getInsert b y (m.insert a x))
        (Eq.sym (Eq.trans (Map.getInsertOther a x b (e => ne (Eq.sym e)) (m.insert b y)) (Map.getInsert b y m)))
    else
      if ha: key = a then
        rewrite ha in
        Eq.trans (Eq.trans (Map.getInsertOther b y a ne (m.insert a x)) (Map.getInsert a x m))
          (Eq.sym (Map.getInsert a x (m.insert b y)))
      else
        Eq.trans (Eq.trans (Map.getInsertOther b y key hb (m.insert a x)) (Map.getInsertOther a x key ha m))
          (Eq.sym (Eq.trans (Map.getInsertOther a x key ha (m.insert b y)) (Map.getInsertOther b y key hb m))))

--| Inserting the value a key already has changes nothing.
theorem Map.insertGet [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (h: Map.get m key = Some value): Map.insert m key value = m :=
  Map.ext (m.insert key value) m (other =>
    if e: other = key then rewrite e in Eq.trans (Map.getInsert key value m) (Eq.sym h)
    else Map.getInsertOther key value other e m)

--| Inserting at a key twice keeps the second value.
theorem Map.insertInsert [auto ord: Ord k] (key: k) (x: v) (y: v) (m: Map k v):
    (m |> Map.insert key x |> Map.insert key y) = Map.insert m key y :=
  Map.ext ((m.insert key x).insert key y) (m.insert key y) (other =>
    if e: other = key then rewrite e in Eq.trans (Map.getInsert key y (m.insert key x)) (Eq.sym (Map.getInsert key y m))
    else
      Eq.trans (Map.getInsertOther key y other e (m.insert key x))
        (Eq.trans (Map.getInsertOther key x other e m) (Eq.sym (Map.getInsertOther key y other e m))))

--| Removing a key just inserted removes it from the map before.
theorem Map.removeInsert [auto ord: Ord k] (key: k) (value: v) (m: Map k v):
    (m |> Map.insert key value |> Map.remove key) = Map.remove m key :=
  Map.ext ((m.insert key value).remove key) (m.remove key) (other =>
    if e: other = key then rewrite e in Eq.trans (Map.getRemove (m.insert key value) key) (Eq.sym (Map.getRemove m key))
    else
      Eq.trans (Map.getRemoveOther (m.insert key value) key other e)
        (Eq.trans (Map.getInsertOther key value other e m) (Eq.sym (Map.getRemoveOther m key other e))))

-- Induction over maps

--| [`Map.induction`] on the map whose entries are `xs`: take the first entry
--| off, and the rest is the smaller map it was inserted into.
theorem Map.inductionToList [auto ord: Ord k] [p: Map k v → Prop] (base: p Map.empty)
    (step: ∀ (key: k) (value: v) (m: Map k v) => p m → Map.get m key = None → p (Map.insert m key value))
    (xs: List (k, v)) (m: Map k v) (h: Map.toList m = xs): p m :=
  match xs with
    | [] => rewrite Map.toListInjective m Map.empty h in base
    | [(kk, vv), ..rest] =>
      let found: Map.get m kk = Some vv :=
        Eq.trans (Map.getToList m kk) (Eq.trans (Eq.cong (Map.Tree.lookupList kk) h) (Map.Spec.lookupHead kk vv rest))
      let back: Map.insert (Map.remove m kk) kk vv = m :=
        Map.ext ((m.remove kk).insert kk vv) m (other =>
          if e: other = kk then rewrite e in Eq.trans (Map.getInsert kk vv (m.remove kk)) (Eq.sym found)
          else Eq.trans (Map.getInsertOther kk vv other e (m.remove kk)) (Map.getRemoveOther m kk other e))
      let smaller: Map.toList (Map.remove m kk) = rest :=
        Eq.trans (Map.toListRemove m kk) (Eq.trans (Eq.cong (Map.Spec.remove kk) h) (Map.Spec.removeEqual kk kk vv rest (Ord.compareSelf kk)))
      rewrite Eq.sym back in
      step kk vv (Map.remove m kk) (Map.inductionToList [p := p] base step rest (Map.remove m kk) smaller) (Map.getRemove m kk)

--| To prove something of every map, prove it of the empty map, and of a map
--| with a new key inserted, given it of the map before.
theorem Map.induction [auto ord: Ord k] [p: Map k v → Prop] (base: p Map.empty)
    (step: ∀ (key: k) (value: v) (m: Map k v) => p m → Map.get m key = None → p (Map.insert m key value)) (m: Map k v): p m :=
  Map.inductionToList [p := p] base step (Map.toList m) m rfl

--| A small map for the tests below: 1, 2 and 3 to "a", "b" and "c".
def Map.example: Map Nat Text := Map.fromList [(3, "c"), (1, "a"), (2, "b")]

test "map: toList is in key order" := Map.toList Map.example == [(1, "a"), (2, "b"), (3, "c")]
test "map: get" := Map.get Map.example 2 == Some "b" ∧ Map.get Map.example 4 == None
test "map: getOr" := Map.getOr Map.example 4 "?" == "?"
test "map: contains" := Map.contains Map.example 1 ∧ ¬(Map.contains Map.example 0)
test "map: insert replaces" := Map.toList (Map.insert Map.example 2 "B") == [(1, "a"), (2, "B"), (3, "c")]
test "map: insertWith counts" :=
  Map.toList (List.foldLeft ['b', 'a', 'b'] Map.empty (m c => Map.insertWith m c 1 Nat.add)) == [('a', 1), ('b', 2)]
test "map: remove" := Map.toList (Map.remove Map.example 2) == [(1, "a"), (3, "c")] ∧ Map.size (Map.remove Map.example 9) == 3
test "map: alter" := Map.toList (Map.alter (Map.alter Map.example 4 (old => Some "d")) 1 (old => None)) == [(2, "b"), (3, "c"), (4, "d")]
test "map: adjust" := Map.get (Map.adjust Map.example 3 (t => Text.append t "!")) 3 == Some "c!"
test "map: size" := Map.size Map.example == 3 ∧ Map.isEmpty (Map.empty: Map Nat Nat)
test "map: size after insert and remove" :=
  Map.size (Map.insert Map.example 2 "B") == 3 ∧ Map.size (Map.insert Map.example 4 "d") == 4
    ∧ Map.size (Map.remove Map.example 2) == 2 ∧ Map.size (Map.remove Map.example 4) == 3
    ∧ Map.size (Map.remove (Map.empty: Map Nat Nat) 1) == 0
test "map: toList holds what get finds" := List.all (Map.toList Map.example) (e => Map.get Map.example e.fst == Some e.snd)
test "map: keys and values" := Map.keys Map.example == [1, 2, 3] ∧ Map.values Map.example == ["a", "b", "c"]
test "map: fromList, later wins" := Map.toList (Map.fromList [(1, 1), (1, 2)]) == [(1, 2)]
test "map: List.toMap" := [(3, "c"), (1, "a"), (2, "b"), (1, "z")].toMap == Map.fromList [(1, "z"), (2, "b"), (3, "c")]
test "map: foldLeft" := Map.foldLeft Map.example 0 (acc key t => acc + key) == 6
test "map: map" := Map.values (Map.map Map.example Text.length) == [1, 1, 1]
test "map: get after map" := Map.get (Map.map Map.example Text.length) 2 == Some 1 ∧ Map.get (Map.map Map.example Text.length) 4 == None
test "map: filter" := Map.keys (Map.filter Map.example (key t => Nat.leq 2 key)) == [2, 3]
test "map: union" := Map.toList (Map.union (Map.singleton 1 "x") Map.example) == [(1, "x"), (2, "b"), (3, "c")]
test "map: show" := "${Map.example}" == "Map.fromList [(1, \"a\"), (2, \"b\"), (3, \"c\")]"
test "map: equal in any order" :=
  Map.example == Map.fromList [(1, "a"), (2, "b"), (3, "c")] ∧ Map.example ≠ Map.insert Map.example 2 "B"
test "map: ordered by entries" := Map.insert Map.example 2 "B" < Map.example ≤ Map.fromList [(2, "b"), (1, "a"), (3, "c")]

--| A larger map for the tests below: 1, 2, 3, 5 and 7 to their letters.
def Map.example2: Map Nat Text := Map.fromList [(3, "c"), (1, "a"), (2, "b"), (7, "g"), (5, "e")]

test "map: fromListWith combines in list order" :=
  Map.toList (Map.fromListWith [(1, "a"), (2, "b"), (1, "c")] (new old => Text.append old new)) == [(1, "ac"), (2, "b")]
test "map: groupBy keeps list order" :=
  Map.toList (Map.groupBy [1, 2, 3, 4, 5, 6] (n => n % 3)) |> .map (entry => (entry.fst, entry.snd.toList)) == [(0, [3, 6]), (1, [1, 4]), (2, [2, 5])]
test "map: List.groupBy" :=
  Map.toList ([1, 2, 3, 4, 5, 6].groupBy (n => n % 3)) |> .map (entry => (entry.fst, entry.snd.toList)) == [(0, [3, 6]), (1, [1, 4]), (2, [2, 5])]
test "map: groupMap keeps list order" :=
  Map.toList (Map.groupMap [(1, "a"), (2, "b"), (1, "c"), (3, "d")] Pair.fst Pair.snd) |> .map (entry => (entry.fst, entry.snd.toList)) == [(1, ["a", "c"]), (2, ["b"]), (3, ["d"])]
test "map: List.groupMap" :=
  Map.toList ([(1, "a"), (2, "b"), (1, "c")].groupMap Pair.fst Pair.snd) |> .map (entry => (entry.fst, entry.snd.toList)) == [(1, ["a", "c"]), (2, ["b"])]
test "map: groupMap empty" := Map.isEmpty (Map.groupMap ([]: List (Nat, Text)) Pair.fst Pair.snd)
test "map: indexBy keeps the first" := Map.toList (Map.indexBy ["ab", "c", "de", "f"] Text.length) == [(1, "c"), (2, "ab")]
test "map: indexBy empty" := Map.toList (Map.indexBy [] Text.length) == []
test "map: counts" := Map.toList (Map.counts ['b', 'a', 'b']) == [('a', 1), ('b', 2)]
test "map: find" := Map.find Map.example2 (key t => key > 2) == Some (3, "c") ∧ Map.find Map.example2 (key t => key > 7) == None
test "map: min and max" :=
  Map.min Map.example2 == Some (1, "a") ∧ Map.max Map.example2 == Some (7, "g") ∧ Map.min (Map.empty: Map Nat Nat) == None
test "map: popMin" :=
  Map.popMin Map.example2 == Some ((1, "a"), Map.remove Map.example2 1) ∧ Map.popMin (Map.empty: Map Nat Nat) == None
test "map: below" :=
  Map.below Map.example2 5 == Some (3, "c") ∧ Map.below Map.example2 6 == Some (5, "e") ∧ Map.below Map.example2 1 == None
    ∧ Map.below Map.example2 100 == Some (7, "g")
test "map: above" :=
  Map.above Map.example2 5 == Some (7, "g") ∧ Map.above Map.example2 0 == Some (1, "a") ∧ Map.above Map.example2 7 == None
    ∧ Map.above Map.example2 4 == Some (5, "e")
test "map: unionWith" := Map.toList (Map.unionWith (Map.fromList [(1, 10), (2, 20)]) (Map.fromList [(2, 1), (3, 1)]) Nat.add) == [(1, 10), (2, 21), (3, 1)]
test "map: intersectWith" := Map.toList (Map.intersectWith Map.example2 (Map.fromList [(2, 20), (4, 40), (5, 50)]) (t n => n)) == [(2, 20), (5, 50)]
test "map: difference" := Map.keys (Map.difference Map.example2 (Map.fromList [(2, ()), (5, ())])) == [1, 3, 7]
test "map: combining with an empty map" :=
  Map.toList (Map.union Map.empty Map.example2) == Map.toList Map.example2
    ∧ Map.toList (Map.union Map.example2 Map.empty) == Map.toList Map.example2
    ∧ Map.isEmpty (Map.intersectWith Map.example2 (Map.empty: Map Nat Text) (t u => t))
    ∧ Map.isEmpty (Map.intersectWith (Map.empty: Map Nat Text) Map.example2 (t u => t))
    ∧ Map.toList (Map.difference Map.example2 (Map.empty: Map Nat Text)) == Map.toList Map.example2
    ∧ Map.isEmpty (Map.difference (Map.empty: Map Nat Text) Map.example2)
test "map: combining disjoint maps" :=
  Map.toList (Map.union Map.example (Map.fromList [(0, "z"), (9, "y")])) == [(0, "z"), (1, "a"), (2, "b"), (3, "c"), (9, "y")]
    ∧ Map.isEmpty (Map.intersectWith Map.example (Map.fromList [(0, "z"), (9, "y")]) (t u => t))
    ∧ Map.toList (Map.difference Map.example (Map.fromList [(0, "z"), (9, "y")])) == Map.toList Map.example
test "map: combining a map with itself" :=
  Map.toList (Map.unionWith Map.example Map.example Text.append) == [(1, "aa"), (2, "bb"), (3, "cc")]
    ∧ Map.toList (Map.intersectWith Map.example Map.example Text.append) == [(1, "aa"), (2, "bb"), (3, "cc")]
    ∧ Map.isEmpty (Map.difference Map.example Map.example)
test "map: union keeps the first map's value where keys overlap" :=
  Map.toList (Map.union (Map.fromList [(2, "x"), (4, "y")]) Map.example) == [(1, "a"), (2, "x"), (3, "c"), (4, "y")]
    ∧ Map.toList (Map.union Map.example (Map.fromList [(2, "x"), (4, "y")])) == [(1, "a"), (2, "b"), (3, "c"), (4, "y")]
test "map: unionWith passes the first map's value first" :=
  Map.toList (Map.unionWith (Map.fromList [(1, 10), (2, 20)]) (Map.fromList [(2, 1), (3, 1)]) Nat.sub) == [(1, 10), (2, 19), (3, 1)]
    ∧ Map.toList (Map.unionWith (Map.fromList [(2, "x")]) Map.example2 Text.append) == [(1, "a"), (2, "xb"), (3, "c"), (5, "e"), (7, "g")]
    ∧ Map.toList (Map.unionWith Map.example2 (Map.fromList [(2, "x")]) Text.append) == [(1, "a"), (2, "bx"), (3, "c"), (5, "e"), (7, "g")]
test "map: intersectWith passes the first map's value first" :=
  Map.toList (Map.intersectWith (Map.fromList [(1, 10), (2, 20)]) (Map.fromList [(2, 1), (3, 1)]) Nat.sub) == [(2, 19)]
test "map: mapWithKey" :=
  Map.toList (Map.mapWithKey Map.example2 (key t => Text.append t (Nat.toText key))) == [(1, "a1"), (2, "b2"), (3, "c3"), (5, "e5"), (7, "g7")]
test "map: filterMap" := Map.toList (Map.filterMap Map.example2 (key t => if key > 2 then Some key else None)) == [(3, 3), (5, 5), (7, 7)]
test "map: partition" :=
  Map.keys (Map.partition Map.example2 (key t => key > 2)).fst == [3, 5, 7] ∧ Map.keys (Map.partition Map.example2 (key t => key > 2)).snd == [1, 2]
test "map: mapKeys, later wins" := Map.toList (Map.mapKeys Map.example2 (key => key / 2)) == [(0, "a"), (1, "c"), (2, "e"), (3, "g")]
test "map: foldRight" := Map.foldRight Map.example2 "" (key t acc => Text.append t acc) == "abceg"
test "map: any, all, count" :=
  Map.any Map.example2 (key t => key == 5) ∧ ¬(Map.all Map.example2 (key t => key < 7)) ∧ Map.count Map.example2 (key t => key > 2) == 3
test "map: range" := Map.keys (Map.range Map.example2 2 6) == [2, 3, 5] ∧ Map.keys (Map.range Map.example2 6 2) == []

--| Each element of a list by its position, counting from 0, for lookup in
--| O(log n): `Map.byPosition ["a", "b"]` maps 0 to "a" and 1 to "b".
def Map.byPosition (xs: List a): Map Nat a := xs.withIndex |> .toMap

test "map: byPosition" := Map.toList (Map.byPosition ["a", "b"]) == [(0, "a"), (1, "b")] ∧ Map.get (Map.byPosition ["a", "b"]) 2 == None
