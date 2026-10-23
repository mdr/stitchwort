-- Maps with the same entries, whatever order they were built in
-- (std/Map/Spec.sw, std/Set/Spec.sw; docs/proposals/map-equality.md, "Stage 0
-- results"). `Map.same` decides `Map.Equiv`, "the same entries in key order";
-- each operation respects it, and the agreement lemmas say what each does to
-- `toList`.

import Std (Bool, Eq, List, Map, Nat, Set)

-- The same entries, inserted in different orders: different trees, the same map.
def forwards: Map Nat Text := Map.fromList [(1, "a"), (2, "b"), (3, "c"), (4, "d")]
def backwards: Map Nat Text := Map.fromList [(4, "d"), (3, "c"), (2, "b"), (1, "a")]

test "insertion order doesn't matter" := Map.same forwards backwards
test "a changed value does" := !(Map.same forwards (backwards.insert 2 "B"))
test "an extra key does" := !(Map.same forwards (backwards.insert 5 "e"))
test "removing and putting back" := Map.same forwards ((forwards.remove 3).insert 3 "c")
test "size is the number of entries" :=
  ((forwards.remove 2).insert 9 "z").size == ((forwards.remove 2).insert 9 "z").toList.length

-- A record with a map in it: compared field by field, the map with `Map.same`.
type Stock = { owner: Text, counts: Map Text Nat }

def Stock.same (a: Stock) (b: Stock): Bool := a.owner == b.owner && Map.same a.counts b.counts

def morning: Stock := { owner = "Ada", counts = Map.fromList [("nails", 3), ("screws", 5)] }
def evening: Stock := { owner = "Ada", counts = (Map.fromList [("screws", 5)]).insert "nails" 3 }

test "records with maps" := morning.same evening && !(morning.same { owner = "Bo", counts = evening.counts })

-- Sets: the same keys.
test "sets in any order" := Set.same (Set.fromList [3, 1, 2]: Set Nat) (Set.fromList [2, 3, 1, 1])
test "sets differ" := !(Set.same (Set.fromList [1, 2]: Set Nat) (Set.fromList [1, 3]))

-- Proofs. `size` counts the entries, for every map.
theorem sizeIsLength (m: Map Text Nat): m.size = m.toList.length := Map.sizeToList m

-- Equivalent maps answer every question the same way, after the same changes.
theorem sameAfterInsert (m: Map Text Nat) (n: Map Text Nat) (h: Map.Equiv m n):
    (m.insert "nails" 3).get "screws" = (n.insert "nails" 3).get "screws" :=
  Map.getRespects "screws" (m.insert "nails" 3) (n.insert "nails" 3) (Map.insertRespects "nails" 3 m n h)

theorem sameSizeAfterRemove (m: Map Text Nat) (n: Map Text Nat) (h: Map.Equiv m n):
    (m.remove "nails").size = (n.remove "nails").size :=
  Map.sizeRespects (m.remove "nails") (n.remove "nails") (Map.removeRespects "nails" m n h)

-- Inserting two different keys in either order gives equivalent maps, for
-- any map: they agree on `get` everywhere (`Map.equivOfGet`).
theorem insertSwap [auto ord: Ord k] (m: Map k v) (a: k) (x: v) (b: k) (y: v) (ne: Not (a = b)):
    Map.Equiv ((m.insert a x).insert b y) ((m.insert b y).insert a x) :=
  Map.equivOfGet ((m.insert a x).insert b y) ((m.insert b y).insert a x) (key =>
    match DecEq.decide key b with
      | Yes hb =>
        rewrite hb in
        Eq.trans (Map.getInsert b y (m.insert a x))
          (Eq.sym (Eq.trans (Map.getInsertOther a x b (e => ne (Eq.sym e)) (m.insert b y)) (Map.getInsert b y m)))
      | No hb =>
        match DecEq.decide key a with
          | Yes ha =>
            rewrite ha in
            Eq.trans (Eq.trans (Map.getInsertOther b y a ne (m.insert a x)) (Map.getInsert a x m))
              (Eq.sym (Map.getInsert a x (m.insert b y)))
          | No ha =>
            Eq.trans (Eq.trans (Map.getInsertOther b y key hb (m.insert a x)) (Map.getInsertOther a x key ha m))
              (Eq.sym (Eq.trans (Map.getInsertOther a x key ha (m.insert b y)) (Map.getInsertOther b y key hb m))))

-- So their sizes agree too, though the trees can differ.
theorem insertSwapSize (m: Map Text Nat):
    ((m.insert "a" 1).insert "b" 2).size = ((m.insert "b" 2).insert "a" 1).size :=
  Map.sizeRespects ((m.insert "a" 1).insert "b" 2) ((m.insert "b" 2).insert "a" 1)
    (insertSwap m "a" 1 "b" 2 (e => Bool.trueNotFalse (Eq.cong (t => t == "a") e)))

-- `filter` keeps the entries for which the test holds, in key order.
theorem filterInOrder (m: Map Nat Nat):
    (m.filter (key value => value > 2)).toList = m.toList.filter (e => e.snd > 2) :=
  Map.toListFilterList (key value => value > 2) m

-- `Map.same` says yes exactly when the maps are equivalent.
theorem sameMeansEquiv (m: Map Nat Text) (n: Map Nat Text) (h: Map.same m n = True): Map.Equiv m n :=
  Map.sameSound m n h

-- Closed maps: `toList` computes, so `rfl` proves them equivalent (though
-- not equal: their trees differ), and `Map.same` computes too.
theorem forwardsBackwards: Map.Equiv forwards backwards := rfl

theorem sameByComputing: Map.Equiv forwards backwards :=
  Map.sameSound forwards backwards (rfl: Map.same forwards backwards = True)
