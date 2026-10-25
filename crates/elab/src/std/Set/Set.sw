-- `Set k`: finite sets of keys, a `Map` from the keys to `()`, with the
-- ordering in the type as for `Map` (docs/proposals/interfaces.md §7.5):
-- `Set Nat` is `Set Nat [ord := Nat.instOrd]`. A record around the map, not
-- a synonym for it, so that dot notation on a set finds `Set`'s functions
-- (`s.insert 3`, `s.toList`). The map is a quotient, so sets with the same
-- keys are equal and `==` compares keys (docs/proposals/map-equality.md §8).
-- docs/proposals/map-set.md.

type Set (k: Type) [auto ord: Ord k] = { items: Map k () [ord := ord] }

-- No keys.
def Set.empty [auto ord: Ord k]: Set k := { items = Map.empty }

-- With `key` (the same set if it's there already).
def Set.insert [auto ord: Ord k] (set: Set k) (key: k): Set k := { items = Map.insert set.items key () }

def Set.singleton [auto ord: Ord k] (key: k): Set k := Set.insert Set.empty key

def Set.contains [auto ord: Ord k] (set: Set k) (key: k): Bool := Map.contains set.items key

-- Without `key` (the same set if it isn't there).
def Set.remove [auto ord: Ord k] (set: Set k) (key: k): Set k := { items = Map.remove set.items key }

-- The number of keys, O(1).
def Set.size (set: Set k [ord := o]): Nat := Map.size set.items

def Set.isEmpty (set: Set k [ord := o]): Bool := Map.isEmpty set.items

-- The keys, in order.
def Set.toList (set: Set k [ord := o]): List k := Map.keys set.items

def Set.fromList [auto ord: Ord k] (xs: List k): Set k := List.foldLeft xs Set.empty (set key => Set.insert set key)

-- Left fold over the keys in order.
def Set.foldLeft (set: Set k [ord := o]) (initial: b) (f: b -> k -> b): b := Map.foldLeft set.items initial (acc key unit => f acc key)

-- The keys for which `p` holds.
def Set.filter [auto ord: Ord k] (set: Set k) (p: k -> Bool): Set k := { items = Map.filter set.items (key unit => p key) }

-- The keys of both. O(n + m), or O(n log m) when `a` is much smaller
-- (likewise `intersect` and `difference`; see `Map.union`).
def Set.union [auto ord: Ord k] (a: Set k) (b: Set k): Set k := { items = Map.union a.items b.items }

-- The keys of `a` that are also in `b`.
def Set.intersect [auto ord: Ord k] (a: Set k) (b: Set k): Set k := { items = Map.intersectWith a.items b.items (here there => ()) }

-- The keys of `a` that aren't in `b`.
def Set.difference [auto ord: Ord k] (a: Set k) (b: Set k): Set k := { items = Map.difference a.items b.items }

-- The keys of every set in the list.
def Set.unions [auto ord: Ord k] (ss: List (Set k)): Set k := List.foldLeft ss Set.empty Set.union

-- The smallest key, O(log n).
def Set.min (set: Set k [ord := o]): Option k := Option.map (Map.min set.items) Pair.fst

-- The largest key, O(log n).
def Set.max (set: Set k [ord := o]): Option k := Option.map (Map.max set.items) Pair.fst

-- The largest key below `key` (strictly), O(log n).
def Set.below [auto ord: Ord k] (set: Set k) (key: k): Option k := Option.map (Map.below set.items key) Pair.fst

-- The smallest key above `key` (strictly), O(log n).
def Set.above [auto ord: Ord k] (set: Set k) (key: k): Option k := Option.map (Map.above set.items key) Pair.fst

-- Whether every key satisfies `p`.
def Set.all (set: Set k [ord := o]) (p: k -> Bool): Bool := Set.foldLeft set True (acc key => acc && p key)

-- Whether every key of `a` is in `b`.
def Set.isSubset [auto ord: Ord k] (a: Set k) (b: Set k): Bool := Set.all a (key => Set.contains b key)

-- Whether no key is in both.
def Set.disjoint [auto ord: Ord k] (a: Set k) (b: Set k): Bool := !(Set.any a (key => Set.contains b key))

-- The keys for which `p` holds, and those for which it doesn't.
def Set.partition [auto ord: Ord k] (set: Set k) (p: k -> Bool): (Set k, Set k) := (Set.filter set p, Set.filter set (key => !(p key)))

-- Right fold over the keys in order: `f k1 (f k2 initial)`.
def Set.foldRight (set: Set k [ord := o]) (initial: b) (f: k -> b -> b): b := Map.foldRight set.items initial (key unit acc => f key acc)

-- Maps and sets

-- A map's keys, O(n).
def Map.keySet (m: Map k v [ord := o]): Set k [ord := o] := { items = Map.map m (value => ()) }

-- The map from each key of `keys` to `f key`, O(n).
def Map.fromKeys [auto ord: Ord k] (keys: Set k) (f: k -> v): Map k v := Map.mapWithKey keys.items (key unit => f key)

-- The entries whose keys aren't in `ks`.
def Map.removeAll [auto ord: Ord k] (m: Map k v) (ks: Set k): Map k v := Map.filter m (key value => !(Set.contains ks key))

-- The entries whose keys are in `ks`.
def Map.keepOnly [auto ord: Ord k] (m: Map k v) (ks: Set k): Map k v := Map.filter m (key value => Set.contains ks key)

theorem Set.containsInsert [auto ord: Ord k] (key: k) (s: Set k): (s |> Set.insert key |> Set.contains key) = True :=
  rewrite Map.getInsert key () s.items in rfl

-- Equality: the same keys. A set's map is a quotient (std/Map/Map.sw), so
-- sets with the same keys are equal, whatever order they were inserted in.

theorem Set.unitEq: (u: ()) -> (w: ()) -> u = w
  | (), () => rfl

-- Entries whose values are all `()` are fixed by their keys.
theorem Set.unitEntries: (xs: List (k, ())) -> (ys: List (k, ())) -> List.map xs Pair.fst = List.map ys Pair.fst -> xs = ys
  | Nil, Nil, h => rfl
  | Nil, Cons (b, w) ys2, h => Void.exfalso (List.nilNotCons b (List.map ys2 Pair.fst) h)
  | Cons (a, u) xs2, Nil, h => Void.exfalso (List.consNotNil a (List.map xs2 Pair.fst) h)
  | Cons (a, u) xs2, Cons (b, w) ys2, h =>
    rewrite Eq.cong (.headOr a) h, Set.unitEq u w, Set.unitEntries xs2 ys2 (Eq.cong List.tailOf h) in rfl

-- Sets with the same keys in order are equal.
theorem Set.toListInjective: (s: Set k [ord := o]) -> (t: Set k [ord := o]) -> Set.toList s = Set.toList t -> s = t
  | { items = m }, { items = n }, same =>
    Eq.cong (i => ({ items = i }: Set k [ord := o])) (Map.toListInjective m n (Set.unitEntries (Map.toList m) (Map.toList n) same))

-- `==`: compare the keys in order, by the set's ordering.
def Set.decEq (set: Set k [ord := o]) (other: Set k [ord := o]): Decidable (set = other) :=
  match List.decEq o.eq.decide (Set.toList set) (Set.toList other) with
    | Yes same => Yes (Set.toListInjective set other same)
    | No differ => No (same => differ (Eq.cong Set.toList same))

instance Set.instDecEq: DecEq (Set k [ord := o]) := { decide = Set.decEq }

-- `compare`: the keys in order, lexicographically, by the set's ordering.
def Set.compare (set: Set k [ord := o]) (other: Set k [ord := o]): Ordering := List.compareLex o.compare (Set.toList set) (Set.toList other)

instance Set.instOrd: Ord (Set k [ord := o]) :=
  Ord.fromCompare [decEq := Set.instDecEq] Set.compare
    (s t same => Set.toListInjective s t (List.compareLexEqual o.compare o.equal (Set.toList s) (Set.toList t) same))
    (s t => List.compareLexFlip o.compare o.flip (Set.toList s) (Set.toList t))
    (s t u => List.compareLexTrans o.compare o.equal o.trans (Set.toList s) (Set.toList t) (Set.toList u))

-- `Set.fromList [1, 2]`, in order, whatever the ordering.
instance Set.instShow [auto show: Show k]: Show (Set k [ord := o]) :=
  Show.fromText (set => Text.append "Set.fromList " (Show.list (x => Show.toSource x) (Set.toList set)))

def Set.example: Set Nat := Set.fromList [3, 1, 2, 3]

test "set: toList is in order, without repeats" := Set.toList Set.example == [1, 2, 3]
test "set: size" := Set.size Set.example == 3 && Set.isEmpty (Set.empty: Set Nat)
test "set: contains" := Set.contains Set.example 2 && !(Set.contains Set.example 4)
test "set: insert" := Set.toList (Set.insert Set.example 0) == [0, 1, 2, 3] && Set.size (Set.insert Set.example 1) == 3
test "set: remove" := Set.toList (Set.remove Set.example 2) == [1, 3] && Set.size (Set.remove Set.example 7) == 3
test "set: foldLeft" := Set.foldLeft Set.example 0 (acc x => acc * 10 + x) == 123
test "set: union, intersect, difference" :=
  Set.toList (Set.union Set.example (Set.fromList [5, 0])) == [0, 1, 2, 3, 5]
    && Set.toList (Set.intersect Set.example (Set.fromList [2, 3, 4])) == [2, 3]
    && Set.toList (Set.difference Set.example (Set.fromList [2])) == [1, 3]
test "set: union, intersect, difference, edge cases" :=
  Set.toList (Set.union Set.empty Set.example) == [1, 2, 3] && Set.toList (Set.union Set.example Set.empty) == [1, 2, 3]
    && Set.isEmpty (Set.intersect Set.example Set.empty) && Set.isEmpty (Set.intersect Set.empty Set.example)
    && Set.toList (Set.difference Set.example Set.empty) == [1, 2, 3] && Set.isEmpty (Set.difference Set.empty Set.example)
    && Set.toList (Set.intersect Set.example Set.example) == [1, 2, 3] && Set.isEmpty (Set.difference Set.example Set.example)
    && Set.isEmpty (Set.intersect Set.example (Set.fromList [0, 9])) && Set.toList (Set.difference Set.example (Set.fromList [0, 9])) == [1, 2, 3]
test "set: equal in any order" := Set.example == Set.fromList [2, 3, 1] && Set.example != Set.fromList [1, 2]
test "set: ordered by keys" := Set.fromList [1, 2] < Set.example && Set.example <= Set.fromList [3, 2, 1]
test "set: show" := "${Set.fromList ["b", "a"]}" == "Set.fromList [\"a\", \"b\"]"

-- The set of `f` applied to each key; keys that map to the same value merge,
-- and the result is ordered by the new ordering.
def Set.map [auto ord: Ord j] (set: Set k [ord := o]) (f: k -> j): Set j := Set.foldLeft set Set.empty (acc key => Set.insert acc (f key))

-- Whether some key satisfies `p`.
def Set.any (set: Set k [ord := o]) (p: k -> Bool): Bool := Set.foldLeft set False (acc key => acc || p key)

-- The number of keys satisfying `p`.
def Set.count (set: Set k [ord := o]) (p: k -> Bool): Nat := Set.foldLeft set 0 (n key => Nat.succIf n (p key))

test "set: map merges and reorders" := Set.toList (Set.map Set.example (x => 10 - x / 2)) == [9, 10]
test "set: any" := Set.any Set.example (> 2) && Bool.not (Set.any Set.example (> 3)) && Bool.not (Set.any (Set.empty: Set Nat) (x => True))
test "set: count" := Set.count Set.example (!= 2) == 2

test "set: unions" := Set.toList (Set.unions [Set.fromList [3, 1], Set.fromList [2], Set.empty]) == [1, 2, 3]
test "set: min, max, below, above" :=
  Set.min Set.example == Some 1 && Set.max Set.example == Some 3 && Set.min (Set.empty: Set Nat) == None
    && Set.below Set.example 3 == Some 2 && Set.below Set.example 1 == None && Set.above Set.example 1 == Some 2 && Set.above Set.example 3 == None
test "set: isSubset, disjoint" :=
  Set.isSubset (Set.fromList [1, 2]) Set.example && !(Set.isSubset (Set.fromList [1, 4]) Set.example)
    && Set.disjoint Set.example (Set.fromList [4]) && !(Set.disjoint Set.example (Set.fromList [2]))
test "set: isSubset, edge cases" :=
  Set.isSubset Set.empty Set.example && Set.isSubset Set.example Set.example && !(Set.isSubset Set.example Set.empty)
test "set: partition, all, foldRight" :=
  Set.toList (Set.partition Set.example (> 1)).fst == [2, 3] && Set.toList (Set.partition Set.example (> 1)).snd == [1]
    && Set.all Set.example (> 0) && !(Set.all Set.example (> 1)) && Set.foldRight Set.example Nil (n acc => Cons n acc) == [1, 2, 3]
test "map: keySet, fromKeys" :=
  Set.toList (Map.keySet (Map.fromList [(2, "b"), (1, "a")])) == [1, 2] && Map.toList (Map.fromKeys Set.example (* 10)) == [(1, 10), (2, 20), (3, 30)]
test "map: removeAll, keepOnly" :=
  Map.keys (Map.removeAll (Map.fromKeys Set.example (n => n)) (Set.fromList [1, 9])) == [2, 3]
    && Map.keys (Map.keepOnly (Map.fromKeys Set.example (n => n)) (Set.fromList [1, 9])) == [1]
