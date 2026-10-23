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
def Set.insert [auto ord: Ord k] (key: k) (s: Set k): Set k := { items = Map.insert key () s.items }

def Set.singleton [auto ord: Ord k] (key: k): Set k := Set.insert key Set.empty

def Set.contains [auto ord: Ord k] (key: k) (s: Set k): Bool := Map.contains key s.items

-- Without `key` (the same set if it isn't there).
def Set.remove [auto ord: Ord k] (key: k) (s: Set k): Set k := { items = Map.remove key s.items }

-- The number of keys, O(1).
def Set.size (s: Set k [ord := o]): Nat := Map.size s.items

def Set.isEmpty (s: Set k [ord := o]): Bool := Map.isEmpty s.items

-- The keys, in order.
def Set.toList (s: Set k [ord := o]): List k := Map.keys s.items

def Set.fromList [auto ord: Ord k] (xs: List k): Set k := List.foldLeft (s key => Set.insert key s) Set.empty xs

-- Left fold over the keys in order.
def Set.foldLeft (f: b -> k -> b) (z: b) (s: Set k [ord := o]): b := Map.foldLeft (acc key u => f acc key) z s.items

-- The keys for which `p` holds.
def Set.filter [auto ord: Ord k] (p: k -> Bool) (s: Set k): Set k := { items = Map.filter (key u => p key) s.items }

-- The keys of both.
def Set.union [auto ord: Ord k] (a: Set k) (b: Set k): Set k := { items = Map.union a.items b.items }

-- The keys of `a` that are also in `b`.
def Set.intersect [auto ord: Ord k] (a: Set k) (b: Set k): Set k := Set.filter (key => Set.contains key b) a

-- The keys of `a` that aren't in `b`.
def Set.difference [auto ord: Ord k] (a: Set k) (b: Set k): Set k := Set.filter (key => !(Set.contains key b)) a

-- The keys of every set in the list.
def Set.unions [auto ord: Ord k] (ss: List (Set k)): Set k := List.foldLeft Set.union Set.empty ss

-- The smallest key, O(log n).
def Set.min (s: Set k [ord := o]): Option k := Option.map Pair.fst (Map.min s.items)

-- The largest key, O(log n).
def Set.max (s: Set k [ord := o]): Option k := Option.map Pair.fst (Map.max s.items)

-- The largest key below `key` (strictly), O(log n).
def Set.below [auto ord: Ord k] (key: k) (s: Set k): Option k := Option.map Pair.fst (Map.below key s.items)

-- The smallest key above `key` (strictly), O(log n).
def Set.above [auto ord: Ord k] (key: k) (s: Set k): Option k := Option.map Pair.fst (Map.above key s.items)

-- Whether every key satisfies `p`.
def Set.all (s: Set k [ord := o]) (p: k -> Bool): Bool := Set.foldLeft (acc key => acc && p key) True s

-- Whether every key of `a` is in `b`.
def Set.isSubset [auto ord: Ord k] (a: Set k) (b: Set k): Bool := Set.all a (key => Set.contains key b)

-- Whether no key is in both.
def Set.disjoint [auto ord: Ord k] (a: Set k) (b: Set k): Bool := !(Set.any a (key => Set.contains key b))

-- The keys for which `p` holds, and those for which it doesn't.
def Set.partition [auto ord: Ord k] (p: k -> Bool) (s: Set k): (Set k, Set k) := (Set.filter p s, Set.filter (key => !(p key)) s)

-- Right fold over the keys in order: `f k1 (f k2 z)`.
def Set.foldRight (f: k -> b -> b) (z: b) (s: Set k [ord := o]): b := Map.foldRight (key u acc => f key acc) z s.items

-- Maps and sets

-- A map's keys, O(n).
def Map.keySet (m: Map k v [ord := o]): Set k [ord := o] := { items = Map.map (value => ()) m }

-- The map from each key of `ks` to `f key`, O(n).
def Map.fromKeys [auto ord: Ord k] (ks: Set k) (f: k -> v): Map k v := Map.mapWithKey (key u => f key) ks.items

-- The entries whose keys aren't in `ks`.
def Map.removeAll [auto ord: Ord k] (ks: Set k) (m: Map k v): Map k v := Map.filter (key value => !(Set.contains key ks)) m

-- The entries whose keys are in `ks`.
def Map.keepOnly [auto ord: Ord k] (ks: Set k) (m: Map k v): Map k v := Map.filter (key value => Set.contains key ks) m

theorem Set.containsInsert [auto ord: Ord k] (key: k) (s: Set k): (s |> Set.insert key |> Set.contains key) = True :=
  rewrite Map.getInsert key () s.items in rfl

-- Equality: the same keys. A set's map is a quotient (std/Map/Map.sw), so
-- sets with the same keys are equal, whatever order they were inserted in.

theorem Set.unitEq: (u: ()) -> (w: ()) -> u = w
  | (), () => rfl

-- Entries whose values are all `()` are fixed by their keys.
theorem Set.unitEntries: (xs: List (k, ())) -> (ys: List (k, ())) -> List.map Pair.fst xs = List.map Pair.fst ys -> xs = ys
  | Nil, Nil, h => rfl
  | Nil, Cons (b, w) ys2, h => Void.exfalso (List.nilNotCons b (List.map Pair.fst ys2) h)
  | Cons (a, u) xs2, Nil, h => Void.exfalso (List.consNotNil a (List.map Pair.fst xs2) h)
  | Cons (a, u) xs2, Cons (b, w) ys2, h =>
    rewrite Eq.cong (List.headOr a) h, Set.unitEq u w, Set.unitEntries xs2 ys2 (Eq.cong List.tailOf h) in rfl

-- Sets with the same keys in order are equal.
theorem Set.toListInjective: (s: Set k [ord := o]) -> (t: Set k [ord := o]) -> Set.toList s = Set.toList t -> s = t
  | { items = m }, { items = n }, same =>
    Eq.cong (i => ({ items = i }: Set k [ord := o])) (Map.toListInjective m n (Set.unitEntries (Map.toList m) (Map.toList n) same))

-- `==`: compare the keys in order, by the set's ordering.
def Set.decEq (s: Set k [ord := o]) (t: Set k [ord := o]): Decidable (s = t) :=
  match List.decEq o.eq.decide (Set.toList s) (Set.toList t) with
    | Yes same => Yes (Set.toListInjective s t same)
    | No differ => No (same => differ (Eq.cong Set.toList same))

instance Set.instDecEq: DecEq (Set k [ord := o]) := { decide = Set.decEq }

-- `compare`: the keys in order, lexicographically, by the set's ordering.
def Set.compare (s: Set k [ord := o]) (t: Set k [ord := o]): Ordering := List.compareLex o.compare (Set.toList s) (Set.toList t)

instance Set.instOrd: Ord (Set k [ord := o]) :=
  Ord.fromCompare [decEq := Set.instDecEq] Set.compare
    (s t same => Set.toListInjective s t (List.compareLexEqual o.compare o.equal (Set.toList s) (Set.toList t) same))
    (s t => List.compareLexFlip o.compare o.flip (Set.toList s) (Set.toList t))
    (s t u => List.compareLexTrans o.compare o.equal o.trans (Set.toList s) (Set.toList t) (Set.toList u))

-- `Set.fromList [1, 2]`, in order, whatever the ordering.
instance Set.instShow [auto show: Show k]: Show (Set k [ord := o]) :=
  Show.fromText (s => Text.append "Set.fromList " (Show.list (x => Show.toSource x) (Set.toList s)))

def Set.example: Set Nat := Set.fromList [3, 1, 2, 3]

test "set: toList is in order, without repeats" := Set.toList Set.example == [1, 2, 3]
test "set: size" := Set.size Set.example == 3 && Set.isEmpty (Set.empty: Set Nat)
test "set: contains" := Set.contains 2 Set.example && !(Set.contains 4 Set.example)
test "set: insert" := Set.toList (Set.insert 0 Set.example) == [0, 1, 2, 3] && Set.size (Set.insert 1 Set.example) == 3
test "set: remove" := Set.toList (Set.remove 2 Set.example) == [1, 3] && Set.size (Set.remove 7 Set.example) == 3
test "set: foldLeft" := Set.foldLeft (acc x => acc * 10 + x) 0 Set.example == 123
test "set: union, intersect, difference" :=
  Set.toList (Set.union Set.example (Set.fromList [5, 0])) == [0, 1, 2, 3, 5]
    && Set.toList (Set.intersect Set.example (Set.fromList [2, 3, 4])) == [2, 3]
    && Set.toList (Set.difference Set.example (Set.fromList [2])) == [1, 3]
test "set: equal in any order" := Set.example == Set.fromList [2, 3, 1] && Set.example != Set.fromList [1, 2]
test "set: ordered by keys" := Set.fromList [1, 2] < Set.example && Set.example <= Set.fromList [3, 2, 1]
test "set: show" := "${Set.fromList ["b", "a"]}" == "Set.fromList [\"a\", \"b\"]"

-- The set of `f` applied to each key; keys that map to the same value merge,
-- and the result is ordered by the new ordering.
def Set.map [auto ord: Ord j] (s: Set k [ord := o]) (f: k -> j): Set j := Set.foldLeft (acc key => Set.insert (f key) acc) Set.empty s

-- Whether some key satisfies `p`.
def Set.any (s: Set k [ord := o]) (p: k -> Bool): Bool := Set.foldLeft (acc key => acc || p key) False s

-- The number of keys satisfying `p`.
def Set.count (s: Set k [ord := o]) (p: k -> Bool): Nat := Set.foldLeft (n key => Nat.succIf n (p key)) 0 s

test "set: map merges and reorders" := Set.toList (Set.map Set.example (x => 10 - x / 2)) == [9, 10]
test "set: any" := Set.any Set.example (x => x > 2) && Bool.not (Set.any Set.example (x => x > 3)) && Bool.not (Set.any (Set.empty: Set Nat) (x => True))
test "set: count" := Set.count Set.example (x => x != 2) == 2

test "set: unions" := Set.toList (Set.unions [Set.fromList [3, 1], Set.fromList [2], Set.empty]) == [1, 2, 3]
test "set: min, max, below, above" :=
  Set.min Set.example == Some 1 && Set.max Set.example == Some 3 && Set.min (Set.empty: Set Nat) == None
    && Set.below 3 Set.example == Some 2 && Set.below 1 Set.example == None && Set.above 1 Set.example == Some 2 && Set.above 3 Set.example == None
test "set: isSubset, disjoint" :=
  Set.isSubset (Set.fromList [1, 2]) Set.example && !(Set.isSubset (Set.fromList [1, 4]) Set.example)
    && Set.disjoint Set.example (Set.fromList [4]) && !(Set.disjoint Set.example (Set.fromList [2]))
test "set: partition, all, foldRight" :=
  Set.toList (Set.partition (n => n > 1) Set.example).fst == [2, 3] && Set.toList (Set.partition (n => n > 1) Set.example).snd == [1]
    && Set.all Set.example (n => n > 0) && !(Set.all Set.example (n => n > 1)) && Set.foldRight (n acc => Cons n acc) Nil Set.example == [1, 2, 3]
test "map: keySet, fromKeys" :=
  Set.toList (Map.keySet (Map.fromList [(2, "b"), (1, "a")])) == [1, 2] && Map.toList (Map.fromKeys Set.example (n => n * 10)) == [(1, 10), (2, 20), (3, 30)]
test "map: removeAll, keepOnly" :=
  Map.keys (Map.removeAll (Set.fromList [1, 9]) (Map.fromKeys Set.example (n => n))) == [2, 3]
    && Map.keys (Map.keepOnly (Set.fromList [1, 9]) (Map.fromKeys Set.example (n => n))) == [1]
