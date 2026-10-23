# `Map` and `Set` (SW-113): as built

**Status:** built, 21 October 2026 (SW-113). The signatures are
[interfaces.md §7.5](interfaces.md#75-map-and-set-signatures-for-sw-113);
the ordering lives in the type (D169), using stage 3's `Ord` and stage 4's
`auto` parameters on data types. This note records what was built and the
choices made while building it (D212: the tree).

## Using it

```
def wordCounts (words: List Text): Map Text Nat :=
  words.foldLeft ((counts: Map Text Nat) word => counts.insertWith Nat.add word 1) Map.empty

test "counting" := (wordCounts ["b", "a", "b"]).toList == [("a", 1), ("b", 2)]

def seen: Set (Nat, Nat) := Set.fromList [(0, 1), (0, 0), (0, 1)]

test "a set" := seen.size == 2 && seen.contains (0, 0)
```

`Map Text Nat` means `Map Text Nat [ord := Text.instOrd]`, found by search.
Another ordering is passed by name, `Map Nat Text [ord := descending]`, and
gives a different type: every operation on that map uses `descending`, and
passing it where a `Map Nat Text` is expected is `E-TYPE-MISMATCH`, with a
note that the dictionaries differ. Example: `examples/accept/map-set.sw`
(counting, a set of positions, a proof, §7.5's cases), and
`examples/reject/map-ordering-differs.sw`.

| Group | `Map` (`std/Map/Map.sw`) | `Set` (`std/Set/Set.sw`) |
|---|---|---|
| Building | `empty`, `singleton key value`, `insert key value m`, `insertWith f key value m` (stores `f value old` when there is one), `fromList` (a later pair wins) | `empty`, `singleton`, `insert`, `fromList` |
| Looking up | `get key m: Maybe v`, `getOr d key m`, `contains key m` | `contains` |
| Changing | `remove key m`, `alter f key m` (`f: Maybe v -> Maybe v`; `Nothing` removes), `adjust f key m`, `map f m`, `filter p m`, `union a b` (`a`'s values win) | `remove`, `filter`, `union`, `intersect`, `difference` |
| Reading out | `size` (O(1)), `isEmpty`, `toList` (in key order), `keys`, `values`, `foldLeft f z m` (`f: b -> k -> v -> b`, in key order) | `size`, `isEmpty`, `toList` (in order), `foldLeft` |
| More (stage 2.2) | `fromListWith`, `groupBy`, `counts`, `fromKeys`, `find`, `min`, `max`, `below`, `above` (O(log n)), `unionWith`, `intersectWith`, `difference`, `mapWithKey`, `filterMap`, `partition`, `mapKeys`, `removeAll`, `keepOnly`, `foldRight`, `any`, `all`, `count`, `range lo hi`, `keySet` | `unions`, `min`, `max`, `below`, `above`, `all`, `isSubset`, `disjoint`, `partition`, `foldRight` |
| Theorems | `Map.getInsert` (§7.5), `Map.getInsertOther` (`Not (other = key)` → `get other` unchanged), `Map.getInsertWith`, `Map.getEmpty` | `Set.containsInsert` |
| `Show` | `Map.fromList [(1, "a"), (2, "b")]`, for any ordering (`Show (Map k v [ord := o])`) | `Set.fromList [1, 2]` |

`insert`, `get`, `contains` and `remove` take O(log n) comparisons. Inserting
10,000 `Nat` keys and then looking each one up takes 2.5 s with
`stitchwort run` (release build, the reference evaluator, 21 October 2026),
of which about 0.2 s is checking the program and the library files.

## As built

1. **The tree (D212): weight-balanced**, Adams's trees as in Haskell's
   `Data.Map` (delta 3, ratio 2), `Bin size left key value right`. The
   size in each node makes `size` O(1). Rebalancing is split in two:
   `Map.Tree.shape` picks a rotation (`Keep`, `SingleL`, `DoubleL`,
   `SingleR`, `DoubleR`) from the sizes alone, and `Map.Tree.rebuild`
   performs it, falling back to a plain node when the tree's shape doesn't
   fit the rotation. So the proofs that keys stay in order are about
   `rebuild` for every shape, and never look at the sizes: that is what
   made weight-balanced (or AVL, whose heights would play the same part)
   easier than red-black, whose balancing is a match with overlapping cases
   that the proofs would have to mirror. Balance itself is not proved
   (performance only, as the ticket allows).
2. **"In order" is bounds.** `Map.Tree.Within ord lo hi t` says every key is
   strictly between `lo` and `hi` (`Maybe k`, `Nothing` unbounded) and each
   subtree is within its parent's key; `Map.Tree.Ordered ord t` is
   `Within ord Nothing Nothing t`. With bounds, a rotation needs only
   transitivity at the keys it moves (`aboveTrans`, `belowTrans`), not a
   lemma over whole subtrees. `insertWith`, `remove` (through `deleteMin`
   and `glue`) and `map` are proved to keep it, so `Map` is the record of
   §7.5, `{ tree: Map.Tree k v, ordered: Map.Tree.Ordered ord tree }`.
3. **What `get` finds** is proved through the entries in order:
   `Map.Tree.lookupOnto` says that, for a tree within bounds, searching
   `toListOnto t acc` finds `get`'s answer first. Rotations don't change
   the entries (`rebuildOnto`, each case `rfl`), so `get` on a rebalanced
   node is `get` on the node (`getBalance`), and `getInsertWith` and
   `getInsertWithOther` are then inductions on the tree with no rotation
   cases.
4. **`Set` is a record around a map**, `{ items: Map k () [ord := ord] }`,
   not §7.5's synonym `Map k Unit [ord := ord]`: `Unit` is a proposition
   here, so the value type is `()`, and through a synonym dot notation looks
   in `Map` (interfaces.md stage 4, item 4), so `s.insert 3` would be
   `Map.insert` and `s.toList` would give pairs.
5. **Runtime.** The `ordered` proofs cost little: the bare tree, without
   the record or its proofs, took 2.4 s for the same 10,000 inserts and
   lookups (and a depth count).
6. **Library tests** are named `"map: …"` and `"set: …"`: test names are
   shared by all library files.

Not done, as follow-ups: theorems about `remove` (`get key (remove key m) =
Nothing`, others unchanged), that `toList` is sorted and its keys distinct,
balance as a theorem, `DecEq` for maps (it needs equal trees with equal
proofs: proof irrelevance), and a JavaScript boundary for maps
(interfaces.md §10).
