-- What each set operation does to the keys, from `Map`'s (std/Map/Map.sw),
-- and `Set.ext`: sets with the same keys are equal, whatever order the keys
-- were inserted in (a set's map is a quotient, docs/proposals/
-- map-equality.md §8).

import Std (Eq)

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

theorem Set.ext [auto ord: Ord k]: (s: Set k) -> (t: Set k) -> ((key: k) -> Set.contains key s = Set.contains key t) -> s = t
  | { items = m }, { items = n }, h =>
    Eq.cong (i => ({ items = i }: Set k))
      (Map.ext m n (key => Set.presentInjective (Map.get key m) (Map.get key n)
        (Eq.trans (Eq.sym (Set.containsPresent key m)) (Eq.trans (h key) (Set.containsPresent key n)))))

-- Maps and sets

theorem Map.containsKeySet [auto ord: Ord k] (key: k) (m: Map k v): Set.contains key (Map.keySet m) = Map.contains key m :=
  rewrite Map.getMap (value => ()) key m in
  match c: Map.get key m with
    | None => rfl
    | Some value => rfl

theorem Map.getFromKeys [auto ord: Ord k] (ks: Set k) (f: k -> v) (key: k):
    Map.get key (Map.fromKeys ks f) = (if Set.contains key ks then Some (f key) else None) :=
  rewrite Map.getMapWithKey (key2 u => f key2) key ks.items in
  match c: Map.get key ks.items with
    | None => rfl
    | Some u => rfl

theorem Map.getRemoveAll [auto ord: Ord k] (ks: Set k) (key: k) (m: Map k v):
    Map.get key (Map.removeAll ks m) = (if Set.contains key ks then None else Map.get key m) :=
  rewrite Map.getFilter (key2 value => !(Set.contains key2 ks)) key m in
  match c: Set.contains key ks with
    | True =>
      match d: Map.get key m with
        | None => rfl
        | Some value => rfl
    | False =>
      match d: Map.get key m with
        | None => rfl
        | Some value => rfl

theorem Map.getKeepOnly [auto ord: Ord k] (ks: Set k) (key: k) (m: Map k v):
    Map.get key (Map.keepOnly ks m) = (if Set.contains key ks then Map.get key m else None) :=
  rewrite Map.getFilter (key2 value => Set.contains key2 ks) key m in
  match c: Set.contains key ks with
    | True =>
      match d: Map.get key m with
        | None => rfl
        | Some value => rfl
    | False =>
      match d: Map.get key m with
        | None => rfl
        | Some value => rfl

-- The smallest and largest keys, and what `contains` says about each
-- operation

theorem Set.minToList (s: Set k [ord := o]): Set.min s = List.head (Set.toList s) :=
  rewrite Map.minToList s.items in
  match c: Map.toList s.items with
    | Nil => rfl
    | Cons e rest => rfl

theorem Set.maxToList (s: Set k [ord := o]): Set.max s = List.last (Set.toList s) :=
  rewrite Map.maxToList s.items in Set.lastMapFst (Map.toList s.items)

theorem Set.lastMapFst: (xs: List (k, ())) -> Option.map Pair.fst (List.last xs) = List.last (List.map Pair.fst xs)
  | Nil => rfl
  | Cons e Nil => rfl
  | Cons e (Cons f rest) => Set.lastMapFst (Cons f rest)

theorem Set.containsRemove [auto ord: Ord k] (key: k) (s: Set k): Set.contains key (Set.remove key s) = False :=
  rewrite Map.getRemove key s.items in rfl

theorem Set.containsRemoveOther [auto ord: Ord k] (key: k) (other: k) (ne: Not (other = key)) (s: Set k):
    Set.contains other (Set.remove key s) = Set.contains other s :=
  rewrite Map.getRemoveOther key other ne s.items in rfl

theorem Set.containsUnion [auto ord: Ord k] (key: k) (a: Set k) (b: Set k):
    Set.contains key (Set.union a b) = (Set.contains key a || Set.contains key b) :=
  rewrite Map.getUnion key a.items b.items in
  match c: Map.get key a.items with
    | None => rfl
    | Some u => rfl

theorem Set.containsFilter [auto ord: Ord k] (p: k -> Bool) (key: k) (s: Set k):
    Set.contains key (Set.filter p s) = (Set.contains key s && p key) :=
  rewrite Map.getFilter (key2 u => p key2) key s.items in
  match c: Map.get key s.items with
    | None => rfl
    | Some u =>
      match d: p key with
        | True => rfl
        | False => rfl

theorem Set.containsIntersect [auto ord: Ord k] (key: k) (a: Set k) (b: Set k):
    Set.contains key (Set.intersect a b) = (Set.contains key a && Set.contains key b) :=
  Set.containsFilter (key2 => Set.contains key2 b) key a

theorem Set.containsDifference [auto ord: Ord k] (key: k) (a: Set k) (b: Set k):
    Set.contains key (Set.difference a b) = (Set.contains key a && !(Set.contains key b)) :=
  Set.containsFilter (key2 => !(Set.contains key2 b)) key a
