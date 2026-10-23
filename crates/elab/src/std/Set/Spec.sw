-- `Set.Equiv`: two sets with the same keys, whatever their trees' shapes,
-- with what each set operation does to the keys and the facts that it
-- respects `Set.Equiv`, from `Map`'s (std/Map/Spec.sw). Stage 0 of
-- docs/proposals/map-equality.md.

import Std (Eq)

-- The same keys: the items maps have the same entries (each value is `()`).
def Set.Equiv (s: Set k [ord := o]) (t: Set k [ord := o]): Prop := Map.Equiv s.items t.items

theorem Set.equivRefl (s: Set k [ord := o]): Set.Equiv s s := rfl

theorem Set.equivSym (s: Set k [ord := o]) (t: Set k [ord := o]) (h: Set.Equiv s t): Set.Equiv t s := Eq.sym h

theorem Set.equivTrans (s: Set k [ord := o]) (t: Set k [ord := o]) (u: Set k [ord := o])
    (h1: Set.Equiv s t) (h2: Set.Equiv t u): Set.Equiv s u :=
  Eq.trans h1 h2

-- What the operations do to the keys in order.

theorem Set.toListInsert [auto ord: Ord k] (key: k) (s: Set k):
    Set.toList (Set.insert key s) = List.map Pair.fst (Map.Spec.insert key () (Map.toList s.items)) :=
  Eq.cong (List.map Pair.fst) (Map.toListInsert key () s.items)

theorem Set.toListRemove [auto ord: Ord k] (key: k) (s: Set k):
    Set.toList (Set.remove key s) = List.map Pair.fst (Map.Spec.remove key (Map.toList s.items)) :=
  Eq.cong (List.map Pair.fst) (Map.toListRemove key s.items)

theorem Set.sizeToList (s: Set k [ord := o]): Set.size s = List.length (Set.toList s) :=
  Eq.trans (Map.sizeToList s.items) (Eq.sym (List.lengthMap Pair.fst (Map.toList s.items)))

-- `contains` is `get` finding `()`, so the same `contains` everywhere means
-- the same keys.
theorem Set.unitEq: (u: ()) -> (w: ()) -> u = w
  | (), () => rfl

def Set.present: Option () -> Bool
  | Some u => True
  | None => False

theorem Set.containsPresent [auto ord: Ord k] (key: k) (m: Map k ()): Map.contains key m = Set.present (Map.get key m) :=
  match c: Map.get key m with
    | None => rfl
    | Some u => rfl

theorem Set.presentInjective: (x: Option ()) -> (y: Option ()) -> Set.present x = Set.present y -> x = y
  | None, None, h => rfl
  | None, Some w, h => Void.exfalso (Bool.falseNotTrue h)
  | Some u, None, h => Void.exfalso (Bool.trueNotFalse h)
  | Some u, Some w, h => Eq.cong Some (Set.unitEq u w)

theorem Set.equivOfContains [auto ord: Ord k] (s: Set k) (t: Set k)
    (h: (key: k) -> Set.contains key s = Set.contains key t): Set.Equiv s t :=
  Map.equivOfGet s.items t.items (key => Set.presentInjective (Map.get key s.items) (Map.get key t.items)
    (Eq.trans (Eq.sym (Set.containsPresent key s.items)) (Eq.trans (h key) (Set.containsPresent key t.items))))

-- Entries whose values are all `()` are fixed by their keys.
theorem Set.unitEntries: (xs: List (k, ())) -> (ys: List (k, ())) -> List.map Pair.fst xs = List.map Pair.fst ys -> xs = ys
  | Nil, Nil, h => rfl
  | Nil, Cons (b, w) ys2, h => Void.exfalso (List.nilNotCons b (List.map Pair.fst ys2) h)
  | Cons (a, u) xs2, Nil, h => Void.exfalso (List.consNotNil a (List.map Pair.fst xs2) h)
  | Cons (a, u) xs2, Cons (b, w) ys2, h =>
    rewrite Eq.cong (List.headOr a) h, Set.unitEq u w, Set.unitEntries xs2 ys2 (Eq.cong List.tailOf h) in rfl

theorem Set.equivOfToList (s: Set k [ord := o]) (t: Set k [ord := o]) (h: Set.toList s = Set.toList t): Set.Equiv s t :=
  Set.unitEntries (Map.toList s.items) (Map.toList t.items) h

-- Each operation respects `Set.Equiv`.

theorem Set.containsRespects [auto ord: Ord k] (key: k) (s: Set k) (t: Set k) (h: Set.Equiv s t):
    Set.contains key s = Set.contains key t :=
  Map.containsRespects key s.items t.items h

theorem Set.toListRespects (s: Set k [ord := o]) (t: Set k [ord := o]) (h: Set.Equiv s t): Set.toList s = Set.toList t :=
  Map.keysRespects s.items t.items h

theorem Set.sizeRespects (s: Set k [ord := o]) (t: Set k [ord := o]) (h: Set.Equiv s t): Set.size s = Set.size t :=
  Map.sizeRespects s.items t.items h

theorem Set.isEmptyRespects (s: Set k [ord := o]) (t: Set k [ord := o]) (h: Set.Equiv s t): Set.isEmpty s = Set.isEmpty t :=
  Map.isEmptyRespects s.items t.items h

theorem Set.foldLeftRespects (f: b -> k -> b) (z: b) (s: Set k [ord := o]) (t: Set k [ord := o]) (h: Set.Equiv s t):
    Set.foldLeft f z s = Set.foldLeft f z t :=
  Map.foldLeftRespects (acc key u => f acc key) z s.items t.items h

theorem Set.insertRespects [auto ord: Ord k] (key: k) (s: Set k) (t: Set k) (h: Set.Equiv s t):
    Set.Equiv (Set.insert key s) (Set.insert key t) :=
  Map.insertRespects key () s.items t.items h

theorem Set.removeRespects [auto ord: Ord k] (key: k) (s: Set k) (t: Set k) (h: Set.Equiv s t):
    Set.Equiv (Set.remove key s) (Set.remove key t) :=
  Map.removeRespects key s.items t.items h

theorem Set.filterRespects [auto ord: Ord k] (p: k -> Bool) (s: Set k) (t: Set k) (h: Set.Equiv s t):
    Set.Equiv (Set.filter p s) (Set.filter p t) :=
  Map.filterRespects (key u => p key) s.items t.items h

theorem Set.unionRespects [auto ord: Ord k] (a: Set k) (a2: Set k) (b: Set k) (b2: Set k)
    (ha: Set.Equiv a a2) (hb: Set.Equiv b b2): Set.Equiv (Set.union a b) (Set.union a2 b2) :=
  Map.unionRespects a.items a2.items b.items b2.items ha hb

theorem Set.intersectRespects [auto ord: Ord k] (a: Set k) (a2: Set k) (b: Set k) (b2: Set k)
    (ha: Set.Equiv a a2) (hb: Set.Equiv b b2): Set.Equiv (Set.intersect a b) (Set.intersect a2 b2) :=
  Map.equivTrans (Map.filter (key u => Set.contains key b) a.items) (Map.filter (key u => Set.contains key b) a2.items)
    (Map.filter (key u => Set.contains key b2) a2.items)
    (Map.filterRespects (key u => Set.contains key b) a.items a2.items ha)
    (Map.filterCongr (key u => Set.contains key b) (key u => Set.contains key b2)
      (key u => Set.containsRespects key b b2 hb) a2.items)

theorem Set.differenceRespects [auto ord: Ord k] (a: Set k) (a2: Set k) (b: Set k) (b2: Set k)
    (ha: Set.Equiv a a2) (hb: Set.Equiv b b2): Set.Equiv (Set.difference a b) (Set.difference a2 b2) :=
  Map.equivTrans (Map.filter (key u => !(Set.contains key b)) a.items) (Map.filter (key u => !(Set.contains key b)) a2.items)
    (Map.filter (key u => !(Set.contains key b2)) a2.items)
    (Map.filterRespects (key u => !(Set.contains key b)) a.items a2.items ha)
    (Map.filterCongr (key u => !(Set.contains key b)) (key u => !(Set.contains key b2))
      (key u => rewrite Set.containsRespects key b b2 hb in rfl) a2.items)

-- Deciding `Set.Equiv`: compare the keys in order.
def Set.same (s: Set k [ord := o]) (t: Set k [ord := o]): Bool := Set.toList s == Set.toList t

theorem Set.sameSound (s: Set k [ord := o]) (t: Set k [ord := o]) (h: Set.same s t = True): Set.Equiv s t :=
  Set.equivOfToList s t (Decidable.toBoolSound (DecEq.decide (Set.toList s) (Set.toList t)) h)

theorem Set.sameComplete (s: Set k [ord := o]) (t: Set k [ord := o]) (h: Set.Equiv s t): Set.same s t = True :=
  Decidable.toBoolOf (DecEq.decide (Set.toList s) (Set.toList t)) (Set.toListRespects s t h)

test "set: same in any order" := Set.same (Set.fromList [3, 1, 2]: Set Nat) (Set.fromList [1, 2, 3, 2])
test "set: same sees a missing key" := !(Set.same (Set.fromList [1, 2]: Set Nat) (Set.fromList [1]))
