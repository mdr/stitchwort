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
def Map.ofRaw (r: Map.Raw k v [ord := o]): Map k v [ord := o] := { raw = Quot.mk r }

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

-- The value at `key`, or `d`.
def Map.getOr [auto ord: Ord k] (d: v) (key: k) (m: Map k v): v := Option.getOrElse d (Map.get key m)

def Map.contains [auto ord: Ord k] (key: k) (m: Map k v): Bool := match Map.get key m with
  | Some _ => True
  | None => False

-- The number of entries, O(1).
def Map.size (m: Map k v [ord := o]): Nat := Quot.lift Map.Raw.size (a b same => Map.Raw.sizeRespects a b same) m.raw

def Map.isEmpty (m: Map k v [ord := o]): Bool := Nat.equal (Map.size m) 0

def Map.keys (m: Map k v [ord := o]): List k := List.map Pair.fst (Map.toList m)

def Map.values (m: Map k v [ord := o]): List v := List.map Pair.snd (Map.toList m)

-- Left fold over the entries in key order: `f (f z k1 v1) k2 v2`.
def Map.foldLeft (f: b -> k -> v -> b) (z: b) (m: Map k v [ord := o]): b :=
  Quot.lift (Map.Raw.foldLeft f z) (a b same => Map.Raw.foldLeftRespects f z a b same) m.raw

-- Changing

-- `value` at `key`; if `key` has a value already, `f value old` (so
-- `Map.insertWith Nat.add key 1 counts` counts).
def Map.insertWith [auto ord: Ord k] (f: v -> v -> v) (key: k) (value: v) (m: Map k v): Map k v := {
  raw = Quot.lift
    (r => (Quot.mk (Map.Raw.insertWith f key value r): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.insertWithRespects f key value a b same))
    m.raw
}

-- `value` at `key`, replacing any value there.
def Map.insert [auto ord: Ord k] (key: k) (value: v) (m: Map k v): Map k v := {
  raw = Quot.lift
    (r => (Quot.mk (Map.Raw.insert key value r): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.insertRespects key value a b same))
    m.raw
}

-- Without `key` (the same map if it isn't there).
def Map.remove [auto ord: Ord k] (key: k) (m: Map k v): Map k v := {
  raw = Quot.lift
    (r => (Quot.mk (Map.Raw.remove key r): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.removeRespects key a b same))
    m.raw
}

-- The value at `key` changed by `f`, which sees `None` when there's none
-- and removes the entry by returning `None`.
def Map.alter [auto ord: Ord k] (f: Option v -> Option v) (key: k) (m: Map k v): Map k v := {
  raw = Quot.lift
    (r => (Quot.mk (Map.Raw.alter f key r): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.alterRespects f key a b same))
    m.raw
}

-- The value at `key` changed by `f`, if there is one.
def Map.adjust [auto ord: Ord k] (f: v -> v) (key: k) (m: Map k v): Map k v := {
  raw = Quot.lift
    (r => (Quot.mk (Map.Raw.adjust f key r): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.adjustRespects f key a b same))
    m.raw
}

-- Every value changed by `f`; the keys stay.
def Map.map (f: v -> w) (m: Map k v [ord := o]): Map k w [ord := o] := {
  raw = Quot.lift
    (r => (Quot.mk (Map.Raw.map f r): Quot (Map.Raw k w [ord := o]) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.mapRespects f a b same))
    m.raw
}

-- The entries for which `p` holds.
def Map.filter [auto ord: Ord k] (p: k -> v -> Bool) (m: Map k v): Map k v := {
  raw = Quot.lift
    (r => (Quot.mk (Map.Raw.filter p r): Quot (Map.Raw k v) Map.Raw.Equiv))
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
    (r => Map.unionRaw r b.raw)
    (a1 a2 same =>
      Quot.ind
        [p := q => Map.unionRaw a1 q = Map.unionRaw a2 q]
        (r => Quot.sound (Map.Raw.unionRespects a1 a2 r r same rfl))
        b.raw)
    a.raw
}

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
