--| `Set k`: finite sets of keys, a `Map` from the keys to `()`, with the
--| ordering in the type as for `Map`: `Set Nat` is `Set Nat [ord :=
--| Nat.instOrd]`. A record around the map, not a synonym for it, so that dot
--| notation on a set finds `Set`'s functions (`s.insert 3`, `s.toList`). The
--| map is a quotient, so sets with the same keys are equal and `==` compares
--| keys.
-- (docs/proposals/interfaces.md §7.5)
-- (docs/proposals/map-equality.md §8)
-- docs/proposals/map-set.md.

--| A finite set of keys, ordered by the keys: `Set Nat` is a set of numbers.
type Set (k: Type) [auto ord: Ord k] = { items: Map k () [ord := ord] }

--| The set with no keys.
def Set.empty [auto ord: Ord k]: Set k := { items = Map.empty }

--| With `key` (the same set if it's there already): [`Set.containsInsert`], [`Set.containsInsertOther`].
def Set.insert [auto ord: Ord k] (set: Set k) (key: k): Set k := { items = Map.insert set.items key () }

--| The set with just `key`.
def Set.singleton [auto ord: Ord k] (key: k): Set k := Set.insert Set.empty key

--| Whether `key` is in the set, O(log n).
def Set.contains [auto ord: Ord k] (set: Set k) (key: k): Bool := Map.contains set.items key

--| Without `key` (the same set if it isn't there): [`Set.containsRemove`], [`Set.containsRemoveOther`].
def Set.remove [auto ord: Ord k] (set: Set k) (key: k): Set k := { items = Map.remove set.items key }

--| The number of keys, O(1): the length of `Set.toList` ([`Set.sizeToList`]).
def Set.size (set: Set k [ord := o]): Nat := Map.size set.items

--| Whether the set has no keys.
def Set.isEmpty (set: Set k [ord := o]): Bool := Map.isEmpty set.items

--| The keys, in order, each once; a key is in it exactly when the set contains it ([`Set.memToList`]).
def Set.toList (set: Set k [ord := o]): List k := Map.keys set.items

--| `set.contains key` reads as `key` being one of the set's keys, `key ∈ set.toList`:
--| a fact `set.contains key = True` is taken apart as that, and built from it. (`key ∈ set`
--| is this fact itself, so it can't be the reading; [`Set.memToList`] is the same statement
--| turned round.)
@[reading]
theorem Set.containsReads ∀ [auto ord: Ord k] (set: Set k) (key: k):
    (Set.contains set key = True) ↔ (key ∈ Set.toList set) :=
  { forward = (Map.memKeys set.items key).backward, backward = (Map.memKeys set.items key).forward }

--| `set.contains key = False` reads as `key` not being one of the set's keys.
@[reading]
theorem Set.containsReadsFalse ∀ [auto ord: Ord k] (set: Set k) (key: k):
    (Set.contains set key = False) ↔ key ∉ Set.toList set :=
  {
    forward = h m => Bool.falseNotTrue (Eq.trans (Eq.sym h) ((Map.memKeys set.items key).forward m)),
    backward = no =>
      match c: Set.contains set key with
        | True => Void.exfalso (no ((Map.memKeys set.items key).backward c))
        | False => rfl
  }

--| The set of the list's elements, repeats merged ([`Set.containsFromListIff`]).
def Set.fromList [auto ord: Ord k] (xs: List k): Set k := List.foldLeft xs Set.empty (set key => Set.insert set key)

--| The set of the list's elements, repeats merged: `Set.fromList` with the
--| list first, so `[3, 1, 3].toSet` reads as a method ([`List.toSetFromList`]).
def List.toSet [auto ord: Ord k] (items: List k): Set k := Set.fromList items

--| Left fold over the keys in order.
def Set.foldLeft (set: Set k [ord := o]) (initial: b) (f: b → k → b): b :=
  set.items.foldLeft initial (acc key unit => f acc key)

--| The keys for which `p` holds ([`Set.containsFilter`]).
def Set.filter [auto ord: Ord k] (set: Set k) (p: k → Bool): Set k :=
  { items = Map.filter set.items (key unit => p key) }

--| The keys of both ([`Set.containsUnion`]). O(n + m), or O(n log m) when one set, of n keys, is
--| much smaller (likewise `difference`, and `intersect` when `a` is the
--| smaller; see `Map.union`).
def Set.union [auto ord: Ord k] (a b: Set k): Set k := { items = Map.union a.items b.items }

--| The keys of `a` that are also in `b` ([`Set.containsIntersect`]).
def Set.intersect [auto ord: Ord k] (a b: Set k): Set k :=
  { items = Map.intersectWith a.items b.items (here there => ()) }

--| The keys of `a` that aren't in `b` ([`Set.containsDifference`]).
def Set.difference [auto ord: Ord k] (a b: Set k): Set k := { items = Map.difference a.items b.items }

--| The keys of every set in the list ([`Set.containsUnionAll`]).
def Set.unionAll [auto ord: Ord k] (sets: List (Set k)): Set k := List.foldLeft sets Set.empty Set.union

--| The keys of every set in the list, as a method on the list, so
--| `groups.map answers |> .unionAll` works ([`Set.unionAll`]).
def List.unionAll [auto ord: Ord k] (sets: List (Set k)): Set k := Set.unionAll sets

--| The smallest key, O(log n): the first of `Set.toList` ([`Set.minToList`]).
def Set.min (set: Set k [ord := o]): Option k := set.items.min |> .map Pair.fst

--| The smallest key and the set without it, in one walk, O(log n): `min`
--| and `remove` together ([`Set.popMinSpec`]).
def Set.popMin (set: Set k [ord := o]): Option (k, Set k [ord := o]) :=
  set.items.popMin |> .map (view => (view.fst.fst, ({ items = view.snd }: Set k [ord := o])))

--| The largest key, O(log n).
def Set.max (set: Set k [ord := o]): Option k := set.items.max |> .map Pair.fst

--| The largest key below `key` (strictly), O(log n).
def Set.below [auto ord: Ord k] (set: Set k) (key: k): Option k := set.items.below key |> .map Pair.fst

--| The smallest key above `key` (strictly), O(log n).
def Set.above [auto ord: Ord k] (set: Set k) (key: k): Option k := set.items.above key |> .map Pair.fst

--| Whether every key satisfies `p`.
def Set.all (set: Set k [ord := o]) (p: k → Bool): Bool := Set.foldLeft set True (acc key => acc ∧ p key)

--| Whether no key is in both.
def Set.disjoint [auto ord: Ord k] (a b: Set k): Bool := ¬(a.any (key => b.contains key))

--| The keys for which `p` holds, and those for which it doesn't.
def Set.partition [auto ord: Ord k] (set: Set k) (p: k → Bool): (Set k, Set k) :=
  (set.filter p, set.filter (key => ¬(p key)))

--| Right fold over the keys in order: `f k1 (f k2 initial)`.
def Set.foldRight (set: Set k [ord := o]) (initial: b) (f: k → b → b): b :=
  Map.foldRight set.items initial (key unit acc => f key acc)

-- Maps and sets

--| A map's keys, O(n).
def Map.keySet (m: Map k v [ord := o]): Set k [ord := o] := { items = Map.map m (value => ()) }

--| The map from each key of `keys` to `f key`, O(n).
def Map.fromKeys [auto ord: Ord k] (keys: Set k) (f: k → v): Map k v := Map.mapWithKey keys.items (key unit => f key)

--| The entries whose keys aren't in `ks`.
def Map.removeAll [auto ord: Ord k] (m: Map k v) (ks: Set k): Map k v := m.filter (key value => ¬(ks.contains key))

--| The entries whose keys are in `ks`.
def Map.keepOnly [auto ord: Ord k] (m: Map k v) (ks: Set k): Map k v := Map.filter m (key value => Set.contains ks key)

--| Whether `item` is in the set at `key`: `False` when the map has no entry
--| for `key`.
def Map.containsIn [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v): Bool :=
  m.getOr key Set.empty |> .contains item

--| The map with `item` added to the set at `key`, which starts empty if there
--| is none.
def Map.insertIn [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v): Map k (Set v) :=
  m.alter key (items => items.getOrElse Set.empty |> .insert item |> Some)

--| The map with `item` taken out of the set at `key`. A set left empty is
--| dropped, so maps holding the same pairs are equal.
def Map.removeIn [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v): Map k (Set v) :=
  m.alter key (items => items.map (.remove item) |> .filter (rest => !rest.isEmpty))

theorem Set.containsInsert ∀ [auto ord: Ord k] (key: k) (s: Set k): (s |> Set.insert key |> Set.contains key) = True :=
  rewrite Map.getInsert key () s.items in rfl

theorem List.toSetFromList ∀ [auto ord: Ord k] (items: List k): items.toSet = Set.fromList items := rfl

-- Equality: the same keys. A set's map is a quotient (std/Map/Map.sw), so
-- sets with the same keys are equal, whatever order they were inserted in.

theorem Set.unitEq ∀ (u w: ()): u = w := match u, w with | (), () => rfl

--| Entries whose values are all `()` are fixed by their keys.
theorem Set.unitEntries ∀ (xs ys: List (k, ())) (h: List.map xs Pair.fst = List.map ys Pair.fst): xs = ys :=
  match xs, ys with
    | [], [] => rfl
    | [(a, u), ..xs2], [(b, w), ..ys2] =>
      rewrite Eq.cong (.headOr a) h, Set.unitEq u w, Set.unitEntries xs2 ys2 (Eq.cong List.tailOf h) in rfl

--| Sets with the same keys in order are equal.
theorem Set.toListInjective ∀ (s t: Set k [ord := o]) (same: Set.toList s = Set.toList t): s = t := match s, t with
  | { items = m }, { items = n } =>
    Eq.cong
      (i => ({ items = i }: Set k [ord := o]))
      (Map.toListInjective m n (Set.unitEntries (Map.toList m) (Map.toList n) same))

--| `==`: compare the keys in order, by the set's ordering.
def Set.decEq (set other: Set k [ord := o]): Decidable (set = other) :=
  Decidable.elim
    (List.decEq o.eq.decide (Set.toList set) (Set.toList other))
    (same => Decidable.yes (Set.toListInjective set other same))
    (differ => Decidable.no (same => differ (Eq.cong Set.toList same)))

--| `==` on sets: the same keys.
instance Set.instDecEq: DecEq (Set k [ord := o]) := { decide = Set.decEq }

--| `compare`: the keys in order, lexicographically, by the set's ordering.
def Set.compare (set other: Set k [ord := o]): Ordering := List.compareLex o.compare set.toList other.toList

--| Sets in the order of their key lists, lexicographically (`Set.compare`).
instance Set.instOrd: Ord (Set k [ord := o]) :=
  Ord.fromCompare
    [decEq := Set.instDecEq]
    Set.compare
    (s t same => Set.toListInjective s t (List.compareLexEqual o.compare o.equal (Set.toList s) (Set.toList t) same))
    (s t => List.compareLexFlip o.compare o.flip (Set.toList s) (Set.toList t))
    (s t u => List.compareLexTrans o.compare o.equal o.trans (Set.toList s) (Set.toList t) (Set.toList u))

--| `Set.fromList [1, 2]`, in order, whatever the ordering.
instance Set.instShow [auto show: Show k]: Show (Set k [ord := o]) :=
  Show.fromText (set => Text.append "Set.fromList " (Show.list (x => Show.toSource x) (Set.toList set)))

--| A small set for the tests below: 1, 2 and 3.
def Set.example: Set Nat := Set.fromList [3, 1, 2, 3]

test "set: toList is in order, without repeats" := Set.toList Set.example == [1, 2, 3]
test "set: size" := Set.size Set.example == 3 ∧ Set.isEmpty (Set.empty: Set Nat)
test "set: contains" := Set.contains Set.example 2 ∧ ¬(Set.contains Set.example 4)
test "set: insert" := Set.toList (Set.insert Set.example 0) == [0, 1, 2, 3] ∧ Set.size (Set.insert Set.example 1) == 3
test "set: remove" := Set.toList (Set.remove Set.example 2) == [1, 3] ∧ Set.size (Set.remove Set.example 7) == 3
test "set: foldLeft" := Set.foldLeft Set.example 0 (acc x => acc * 10 + x) == 123
test "set: union, intersect, difference" :=
  Set.toList (Set.union Set.example (Set.fromList [5, 0])) == [0, 1, 2, 3, 5]
    ∧ Set.toList (Set.intersect Set.example (Set.fromList [2, 3, 4])) == [2, 3]
    ∧ Set.toList (Set.difference Set.example (Set.fromList [2])) == [1, 3]
test "set: union, intersect, difference, edge cases" :=
  Set.toList (Set.union Set.empty Set.example) == [1, 2, 3]
    ∧ Set.toList (Set.union Set.example Set.empty) == [1, 2, 3]
    ∧ Set.isEmpty (Set.intersect Set.example Set.empty)
    ∧ Set.isEmpty (Set.intersect Set.empty Set.example)
    ∧ Set.toList (Set.difference Set.example Set.empty) == [1, 2, 3]
    ∧ Set.isEmpty (Set.difference Set.empty Set.example)
    ∧ Set.toList (Set.intersect Set.example Set.example) == [1, 2, 3]
    ∧ Set.isEmpty (Set.difference Set.example Set.example)
    ∧ Set.isEmpty (Set.intersect Set.example (Set.fromList [0, 9]))
    ∧ Set.toList (Set.difference Set.example (Set.fromList [0, 9])) == [1, 2, 3]
test "set: equal in any order" := Set.example == Set.fromList [2, 3, 1] ∧ Set.example ≠ Set.fromList [1, 2]
test "set: ordered by keys" := Set.fromList [1, 2] < Set.example ≤ Set.fromList [3, 2, 1]
test "set: show" := "${Set.fromList ["b", "a"]}" == "Set.fromList [\"a\", \"b\"]"

--| The set of `f` applied to each key ([`Set.containsMap`]); keys that map to
--| the same value merge, and the result is ordered by the new ordering.
def Set.map [auto ord: Ord j] (set: Set k [ord := o]) (f: k → j): Set j :=
  Set.foldLeft set Set.empty (acc key => Set.insert acc (f key))

--| Whether some key satisfies `p`.
def Set.any (set: Set k [ord := o]) (p: k → Bool): Bool := Set.foldLeft set False (acc key => acc ∨ p key)

--| The number of keys satisfying `p`.
def Set.count (set: Set k [ord := o]) (p: k → Bool): Nat := Set.foldLeft set 0 (n key => Nat.succIf n (p key))

test "set: map merges and reorders" := Set.toList (Set.map Set.example (x => 10 - x / 2)) == [9, 10]
test "set: any" :=
  Set.any Set.example (> 2) ∧ Bool.not (Set.any Set.example (> 3)) ∧ Bool.not (Set.any (Set.empty: Set Nat) (x => True))
test "set: count" := Set.count Set.example (≠ 2) == 2

test "set: unionAll" := Set.toList (Set.unionAll [Set.fromList [3, 1], Set.fromList [2], Set.empty]) == [1, 2, 3]
test "set: List.unionAll" := Set.toList ([Set.fromList [3, 1], Set.fromList [2], Set.empty] |> .unionAll) == [1, 2, 3]
test "set: List.toSet" := [3, 1, 3, 2].toSet == Set.example
test "set: min, max, below, above" :=
  Set.min Set.example == Some 1
    ∧ Set.max Set.example == Some 3
    ∧ Set.min (Set.empty: Set Nat) == None
    ∧ Set.below Set.example 3 == Some 2
    ∧ Set.below Set.example 1 == None
    ∧ Set.above Set.example 1 == Some 2
    ∧ Set.above Set.example 3 == None
test "set: popMin" :=
  Set.popMin Set.example == Some (1, Set.fromList [2, 3])
    ∧ Set.popMin (Set.empty: Set Nat) == None
    ∧ (Set.fromList (List.range 0 40) |> .popMin |> .map (view => view.snd.toList))
      == Some (List.range 0 40 |> List.tailOf)
test "set: disjoint" := Set.disjoint Set.example (Set.fromList [4]) ∧ ¬(Set.disjoint Set.example (Set.fromList [2]))
test "set: partition, all, foldRight" :=
  Set.toList (Set.partition Set.example (> 1)).fst == [2, 3]
    ∧ Set.toList (Set.partition Set.example (> 1)).snd == [1]
    ∧ Set.all Set.example (> 0)
    ∧ ¬(Set.all Set.example (> 1))
    ∧ Set.foldRight Set.example [] (n acc => [n, ..acc]) == [1, 2, 3]
test "map: keySet, fromKeys" :=
  Set.toList (Map.keySet (Map.fromList [(2, "b"), (1, "a")])) == [1, 2]
    ∧ Map.toList (Map.fromKeys Set.example (* 10)) == [(1, 10), (2, 20), (3, 30)]
test "map: removeAll, keepOnly" :=
  Map.keys (Map.removeAll (Map.fromKeys Set.example (n => n)) (Set.fromList [1, 9])) == [2, 3]
    ∧ Map.keys (Map.keepOnly (Map.fromKeys Set.example (n => n)) (Set.fromList [1, 9])) == [1]
test "map of sets: containsIn, insertIn, removeIn" :=
  let m: Map Nat (Set Nat) := Map.empty |> .insertIn 1 10 |> .insertIn 1 11 |> .insertIn 2 20
  m.containsIn 1 10
    ∧ m.containsIn 1 11
    ∧ m.containsIn 2 20
    ∧ ¬(m.containsIn 2 10)
    ∧ ¬(m.containsIn 3 10)
    ∧ ¬((m.removeIn 1 10).containsIn 1 10)
    ∧ (m.removeIn 1 10).containsIn 1 11
    ∧ Map.keys (m.removeIn 2 20) == [1]
    ∧ m.removeIn 3 30 == m
    ∧ (m.removeIn 1 10 |> .removeIn 1 11 |> .removeIn 2 20) == Map.empty
