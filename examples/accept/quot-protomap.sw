-- A prototype of `Map` as a quotient (docs/proposals/map-equality.md §8,
-- §14.1 step 1.6): `ProtoMap k v` is a `Map.Raw k v` record (the tree, as
-- `Map` was before stage 2), with two maps identified when they have the
-- same entries (`Map.Raw.Equiv`). Std's `Map` is now built the same way
-- (std/Map/Map.sw); this file keeps the gate's evidence. Each operation is
-- lifted from `Map.Raw`'s with stage 0's respects lemma; `toList` determines a
-- map, so equality is equality of entry lists, for any value type; `DecEq`
-- and `Ord` compare entry lists. Below the prototype, the numbered sections
-- check the gate's properties (§14.2); the others are in
-- reject/quot-protomap-transport-stuck.sw, soundness/quot-protomap-tree.sw,
-- soundness/quot-protomap-recursive.sw and the earlier quot-* examples.
--
--   $ stitchwort run examples/accept/quot-protomap.sw
--   True
--   False
--   True
--   True
--   aBcd
--   5
--   42
--   Greater
--   0

import Std (Eq, Iff, IO, List, Map, Nat, Ord, Quot, Text)
import Std.Map.Tree (Tip, Bin)

type ProtoMap (k: Type) (v: Type) [auto ord: Ord k] = { raw: Quot (Map.Raw k v [ord := ord]) Map.Raw.Equiv }

def ProtoMap.ofMap [auto ord: Ord k] (m: Map.Raw k v): ProtoMap k v := { raw = Quot.mk m }

def ProtoMap.empty [auto ord: Ord k]: ProtoMap k v := ProtoMap.ofMap Map.Raw.empty

def ProtoMap.toList (m: ProtoMap k v [ord := o]): List (k, v) := Quot.lift Map.Raw.toList (a b same => same) m.raw

def ProtoMap.get [auto ord: Ord k] (m: ProtoMap k v) (key: k): Option v :=
  Quot.lift (Map.Raw.get key) (a b same => Map.Raw.getRespects key a b same) m.raw

def ProtoMap.insert [auto ord: Ord k] (m: ProtoMap k v) (key: k) (value: v): ProtoMap k v :=
  { raw = Quot.lift
    (r => (Quot.mk (Map.Raw.insert key value r): Quot (Map.Raw k v) Map.Raw.Equiv))
    (a b same => Quot.sound (Map.Raw.insertRespects key value a b same))
    m.raw
  }

def ProtoMap.size (m: ProtoMap k v [ord := o]): Nat := Quot.lift Map.Raw.size (a b same => Map.Raw.sizeRespects a b same) m.raw

def ProtoMap.isEmpty (m: ProtoMap k v [ord := o]): Bool := Quot.lift Map.Raw.isEmpty (a b same => Map.Raw.isEmptyRespects a b same) m.raw

def ProtoMap.foldLeft (m: ProtoMap k v [ord := o]) (z: b) (f: b → k → v → b): b :=
  Quot.lift (Map.Raw.foldLeft f z) (a b same => Map.Raw.foldLeftRespects f z a b same) m.raw

def ProtoMap.fromList [auto ord: Ord k] (xs: List (k, v)): ProtoMap k v := ProtoMap.ofMap (Map.Raw.fromList xs)

-- Two classes with the same entries are the same class.
theorem ProtoMap.rawInjective (p: Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv) (q: Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv):
    ProtoMap.toList { raw = p } = ProtoMap.toList { raw = q } → p = q :=
  let motive: Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv → Prop :=
    p' => (q': Quot (Map.Raw k v [ord := o]) Map.Raw.Equiv) → ProtoMap.toList { raw = p' } = ProtoMap.toList { raw = q' } → p' = q'
  let fromMk: (a: Map.Raw k v [ord := o]) → motive (Quot.mk a) :=
    a q' =>
      Quot.ind
        [p := q'' => ProtoMap.toList { raw = Quot.mk a } = ProtoMap.toList { raw = q'' } → Quot.mk a = q'']
        (b same => Quot.sound same)
        q'
  Quot.ind [p := motive] fromMk p q

-- Maps with the same entries are equal, whatever their values' type.
theorem ProtoMap.toListInjective: (m: ProtoMap k v [ord := o]) → (n: ProtoMap k v [ord := o]) →
    ProtoMap.toList m = ProtoMap.toList n → m = n
  | { raw = p }, { raw = q }, same => Eq.cong (r => ({ raw = r }: ProtoMap k v [ord := o])) (ProtoMap.rawInjective p q same)

-- Equal maps have the same entries, and maps with the same entries are equal.
theorem ProtoMap.eqIffToListEq (m: ProtoMap k v [ord := o]) (n: ProtoMap k v [ord := o]):
    Iff (m = n) (ProtoMap.toList m = ProtoMap.toList n) := {
      forward = same => Eq.cong ProtoMap.toList same,
      backward = ProtoMap.toListInjective m n
    }

-- What stage 0 proved of every `Map`, for every `ProtoMap`: its entries are
-- in increasing key order, and `get` looks a key up in them.
theorem ProtoMap.toListSorted: (m: ProtoMap k v [ord := o]) → Map.Spec.Sorted o (ProtoMap.toList m)
  | { raw = q } =>
    Quot.ind [p := q' => Map.Spec.Sorted o (ProtoMap.toList { raw = q' })] (a => Map.Raw.toListSorted a) q

theorem ProtoMap.getToList:
    (m: ProtoMap k v [ord := o]) → (key: k) → ProtoMap.get m key = Map.Tree.lookupList key (ProtoMap.toList m)
  | { raw = q }, key =>
    Quot.ind
      [p := q' => ProtoMap.get { raw = q' } key = Map.Tree.lookupList key (ProtoMap.toList { raw = q' })]
      (a => Map.Raw.getToList key a)
      q

-- Maps that agree on every key are equal, whatever their values' type.
theorem ProtoMap.ext (m: ProtoMap k v [ord := o]) (n: ProtoMap k v [ord := o])
    (h: (key: k) → ProtoMap.get m key = ProtoMap.get n key): m = n :=
  ProtoMap.toListInjective m n
    (Map.Spec.extLookup None (ProtoMap.toList m) (ProtoMap.toList n) (ProtoMap.toListSorted m) (ProtoMap.toListSorted n)
      (key => Eq.trans (Eq.sym (ProtoMap.getToList m key)) (Eq.trans (h key) (ProtoMap.getToList n key))))

-- `==`: compare the entry lists. The branch is chosen by the list
-- comparison; `Quot.sound` is only inside the `Yes` proof.
def ProtoMap.decEq [auto dv: DecEq v] (m: ProtoMap k v [ord := o]) (n: ProtoMap k v [ord := o]): Decidable (m = n) :=
  match DecEq.decide (ProtoMap.toList m) (ProtoMap.toList n) with
    | Yes same => Yes (ProtoMap.toListInjective m n same)
    | No differ => No (same => differ (Eq.cong ProtoMap.toList same))

instance ProtoMap.instDecEq [auto dv: DecEq v]: DecEq (ProtoMap k v [ord := o]) := { decide = ProtoMap.decEq }

-- `compare`: the entry lists, in the lists' order. Each law comes from the
-- list order's, `equal` through `toListInjective`.
def ProtoMap.compare [auto vord: Ord v] (m: ProtoMap k v [ord := o]) (n: ProtoMap k v [ord := o]): Ordering :=
  Ord.compare (ProtoMap.toList m) (ProtoMap.toList n)

instance ProtoMap.instOrd [auto vord: Ord v]: Ord (ProtoMap k v [ord := o]) :=
  let lists: Ord (List (k, v)) := List.instOrd
  Ord.fromCompare ProtoMap.compare
    (m n same => ProtoMap.toListInjective m n (lists.equal (ProtoMap.toList m) (ProtoMap.toList n) same))
    (m n => lists.flip (ProtoMap.toList m) (ProtoMap.toList n))
    (m n p => lists.trans (ProtoMap.toList m) (ProtoMap.toList n) (ProtoMap.toList p))

-- 1. Equality computes: the same entries inserted in different orders are
-- `==`, a changed value isn't, in the kernel and in every runner.
def forwards: ProtoMap Nat Text := ProtoMap.fromList [(1, "a"), (2, "b"), (3, "c"), (4, "d")]
def backwards: ProtoMap Nat Text := ProtoMap.fromList [(4, "d"), (3, "c"), (2, "b"), (1, "a")]
def changed: ProtoMap Nat Text := backwards.insert 2 "B"

theorem sameEntriesAreEqual: (forwards == backwards) = True := rfl
theorem aChangedValueIsNot: (forwards == changed) = False := rfl
theorem forwardsIsBackwards: forwards = backwards := ProtoMap.toListInjective forwards backwards rfl

test "insertion order doesn't matter" := forwards == backwards
test "a changed value does" := ¬(forwards == changed)
test "an extra key does" := ¬(forwards == backwards.insert 5 "e")

-- The representatives really are different trees: their roots differ.
def rootKey (m: Map.Raw Nat Text): Option Nat := match m.tree with
  | Tip => None
  | Bin _ _ key _ _ => Some key

theorem forwardsRoot: rootKey (Map.Raw.fromList [(1, "a"), (2, "b"), (3, "c"), (4, "d")]) = Some 2 := rfl
theorem backwardsRoot: rootKey (Map.Raw.fromList [(4, "d"), (3, "c"), (2, "b"), (1, "a")]) = Some 3 := rfl

-- 2. Equality composes: records holding maps, and maps of maps, get `==`
-- with no deriving change.
type Inventory = { owner: Text, counts: ProtoMap Text Nat }

def morning: Inventory := { owner = "Ada", counts = ProtoMap.fromList [("nails", 3), ("screws", 5)] }
def evening: Inventory := { owner = "Ada", counts = (ProtoMap.fromList [("screws", 5)]).insert "nails" 3 }
def other: Inventory := { owner = "Bo", counts = evening.counts }

theorem inventoriesEqual: (morning == evening) = True := rfl
theorem ownersDiffer: (morning == other) = False := rfl

test "records holding maps" := morning == evening ∧ ¬(morning == other)

def nested1: ProtoMap Text (ProtoMap Text Nat) :=
  ProtoMap.fromList [("shed", ProtoMap.fromList [("nails", 3), ("screws", 5)]), ("loft", ProtoMap.fromList [("boxes", 2)])]
def nested2: ProtoMap Text (ProtoMap Text Nat) :=
  (ProtoMap.empty.insert "loft" (ProtoMap.fromList [("boxes", 2)])).insert "shed" (ProtoMap.fromList [("screws", 5), ("nails", 3)])
def nested3: ProtoMap Text (ProtoMap Text Nat) := nested2.insert "shed" (ProtoMap.fromList [("screws", 5)])

theorem nestedEqual: (nested1 == nested2) = True := rfl
theorem nestedDiffer: (nested1 == nested3) = False := rfl

test "maps of maps" := nested1 == nested2 ∧ ¬(nested1 == nested3)

-- 3. Extensionality is general: for function values, with no `DecEq`.
def addOne (x: Nat): Nat := x + 1
def double (x: Nat): Nat := x + x

def fns1: ProtoMap Nat (Nat → Nat) := (ProtoMap.empty.insert 1 addOne).insert 2 double
def fns2: ProtoMap Nat (Nat → Nat) := (ProtoMap.empty.insert 2 double).insert 1 addOne

theorem functionMapsEqual: fns1 = fns2 := ProtoMap.toListInjective fns1 fns2 rfl

theorem functionMapsExt (m: ProtoMap Nat (Nat → Nat)) (n: ProtoMap Nat (Nat → Nat))
    (h: (key: Nat) → ProtoMap.get m key = ProtoMap.get n key): m = n :=
  ProtoMap.ext m n h

theorem functionMapsByEntries (m: ProtoMap Nat (Nat → Nat)) (n: ProtoMap Nat (Nat → Nat))
    (h: ProtoMap.toList m = ProtoMap.toList n): m = n :=
  ProtoMap.toListInjective m n h

-- 4. Ordinary computation survives: lifted operations reduce in the kernel.
theorem getComputes: ProtoMap.get backwards 2 = Some "b" := rfl
theorem getMissing: ProtoMap.get backwards 7 = None := rfl
theorem insertComputes: ProtoMap.toList (backwards.insert 5 "e") = [(1, "a"), (2, "b"), (3, "c"), (4, "d"), (5, "e")] := rfl
theorem sizeComputes: ProtoMap.size (backwards.insert 5 "e") = 5 := rfl
theorem sizeAfterReplace: ProtoMap.size changed = 4 := rfl
theorem foldComputes: ProtoMap.foldLeft backwards 0 (total key value => total + key) = 10 := rfl
theorem emptyComputes: ProtoMap.isEmpty (ProtoMap.empty: ProtoMap Nat Text) = True := rfl
theorem functionValueComputes: (match ProtoMap.get fns1 2 with | Some f => f 5 | None => 0) = 10 := rfl

-- `Ord`: by entry lists.
theorem compareComputes: ProtoMap.compare forwards changed = Greater := rfl
theorem compareEqualMaps: ProtoMap.compare forwards backwards = Equal := rfl

test "ordered by entries" := forwards > changed ∧ ¬(forwards < backwards) ∧ forwards ≤ backwards

-- 7. `size`, `isEmpty` and `foldLeft` lift with stage 0's respects lemmas
-- (above), which rest on the `sized` field; so `size` counts the entries of
-- every map, proved for each representative with `Quot.ind`.
theorem ProtoMap.sizeToList: (m: ProtoMap k v [ord := o]) → ProtoMap.size m = List.length (ProtoMap.toList m)
  | { raw = q } =>
    Quot.ind [p := q' => ProtoMap.size { raw = q' } = List.length (ProtoMap.toList { raw = q' })] (a => Map.Raw.sizeToList a) q

test "size, isEmpty and foldLeft" :=
  ProtoMap.size forwards == 4 ∧ ¬(ProtoMap.isEmpty forwards)
    ∧ ProtoMap.foldLeft forwards 0 (total key value => total + key) == 10

-- 6. Computation limits are deliberate: data transported along a map
-- equality is stuck in the kernel, through `Quot.sound` (§9.1) and through
-- `Quot.ind` alone (§7.4.4), and is `0` when run
-- (reject/quot-protomap-transport-stuck.sw has the `rfl` that fails).
def transported: Nat := J (y p => Nat) 0 forwardsIsBackwards
def transportedByInd: Nat := J (y p => Nat) 0 (ProtoMap.sizeToList forwards)

test "transport runs" := transported == 0 ∧ transportedByInd == 0

def describe (m: ProtoMap Nat Text): Text :=
  ProtoMap.foldLeft m "" (acc key value => Text.append acc value)

def main(): {IO} () :=
  IO.print (if forwards == backwards then "True" else "False")
  IO.print (if forwards == changed then "True" else "False")
  IO.print (if morning == evening then "True" else "False")
  IO.print (if nested1 == nested2 ∧ ¬(nested1 == nested3) then "True" else "False")
  IO.print (describe changed)
  IO.print (Nat.toText (ProtoMap.size (changed.insert 9 "z")))
  IO.print (match ProtoMap.get fns2 2 with
    | Some f => Nat.toText (f 21)
    | None => "none"
  )
  IO.print (if forwards > changed then "Greater" else "not greater")
  IO.print (Nat.toText (transported + transportedByInd))
