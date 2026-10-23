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

theorem Set.containsInsertOther [auto ord: Ord k] (key: k) (other: k) (ne: Not (other = key)) (s: Set k):
    Set.contains other (Set.insert key s) = Set.contains other s :=
  rewrite Map.getInsertOther key () other ne s.items in rfl

-- Inserting the list's keys: `key` is there if it was, or if the list has it.
theorem Set.containsFoldInsert [auto ord: Ord k] (key: k): (xs: List k) -> (s: Set k) ->
    Set.contains key (List.foldLeft (acc x => Set.insert x acc) s xs) = (Set.contains key s || List.any (x => Map.Spec.sameKey key x) xs)
  | Nil, s =>
    match c: Set.contains key s with
      | True => rfl
      | False => rfl
  | Cons x rest, s =>
    rewrite Set.containsFoldInsert key rest (Set.insert x s) in
    match e: Ord.compare key x with
      | Equal =>
        rewrite ord.equal key x e, Set.containsInsert x s in
        match c: Set.contains x s with
          | True => rfl
          | False => rfl
      | Less => rewrite Set.containsInsertOther x key (Map.Spec.notEqualOfCompare key x (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) s in rfl
      | Greater => rewrite Set.containsInsertOther x key (Map.Spec.notEqualOfCompare key x (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) s in rfl

theorem Set.containsFromList [auto ord: Ord k] (key: k) (xs: List k): Set.contains key (Set.fromList xs) = List.any (x => Map.Spec.sameKey key x) xs :=
  Set.containsFoldInsert key xs Set.empty

-- `isSubset`: every key of `a` is in `b`

-- `all`'s fold over a set's entries is `List.all` over them.
theorem Set.foldAll (q: k -> Bool): (z: Bool) -> (xs: List (k, ())) ->
    Map.Spec.foldLeft (acc key unit => acc && q key) z xs = (z && List.all (e => q e.fst) xs)
  | True, Nil => rfl
  | False, Nil => rfl
  | z, Cons (kk, u) rest =>
    rewrite Set.foldAll q (z && q kk) rest in
    match c: z with
      | False => rfl
      | True =>
        match d: q kk with
          | True => rfl
          | False => rfl

theorem Set.allEntriesElim (q: k -> Bool) (key: k): (xs: List (k, ())) -> List.all (e => q e.fst) xs = True -> List.Mem (key, ()) xs -> q key = True
  | Nil, h, mem => Void.exfalso mem
  | Cons (kk, u) rest, h, mem =>
    match c: q kk with
      | False => Void.exfalso (Bool.falseNotTrue h)
      | True =>
        match mem with
          | Inl e => Eq.trans (Eq.cong q (Eq.sym (Eq.cong Pair.fst e))) c
          | Inr later => Set.allEntriesElim q key rest h later

theorem Set.allEntriesIntro (q: k -> Bool): (xs: List (k, ())) -> ((key: k) -> List.Mem (key, ()) xs -> q key = True) -> List.all (e => q e.fst) xs = True
  | Nil, h => rfl
  | Cons (kk, u) rest, h =>
    rewrite h kk (Inl (Eq.cong (w => (kk, w)) (Set.unitEq u ()))) in
    Set.allEntriesIntro q rest (key mem => h key (Inr mem))

theorem Set.isSubsetToList [auto ord: Ord k] (a: Set k) (b: Set k): Set.isSubset a b = List.all (e => Set.contains e.fst b) (Map.toList a.items) :=
  Eq.trans (Map.foldLeftToList (acc key unit => acc && Set.contains key b) True a.items)
    (Set.foldAll (key => Set.contains key b) True (Map.toList a.items))

-- A set has `key` exactly when its map's entries have `(key, ())`.
theorem Set.containsToList [auto ord: Ord k] (key: k) (s: Set k): Iff (Set.contains key s = True) (List.Mem (key, ()) (Map.toList s.items)) := {
  forward = h =>
    match c: Map.get key s.items with
      | None => Void.exfalso (Bool.falseNotTrue h)
      | Some u => (Map.memToList key () s.items).backward (Eq.trans c (Eq.cong Some (Set.unitEq u ()))),
  backward = mem => rewrite (Map.memToList key () s.items).forward mem in rfl
}

theorem Set.isSubsetElim [auto ord: Ord k] (a: Set k) (b: Set k) (h: Set.isSubset a b = True) (key: k) (inA: Set.contains key a = True):
    Set.contains key b = True :=
  Set.allEntriesElim (key2 => Set.contains key2 b) key (Map.toList a.items) (Eq.trans (Eq.sym (Set.isSubsetToList a b)) h)
    ((Set.containsToList key a).forward inA)

theorem Set.isSubsetIntro [auto ord: Ord k] (a: Set k) (b: Set k) (h: (key: k) -> Set.contains key a = True -> Set.contains key b = True):
    Set.isSubset a b = True :=
  Eq.trans (Set.isSubsetToList a b)
    (Set.allEntriesIntro (key2 => Set.contains key2 b) (Map.toList a.items) (key mem => h key ((Set.containsToList key a).backward mem)))

-- `isSubset a b` holds exactly when every key of `a` is in `b`.
theorem Set.isSubsetSpec [auto ord: Ord k] (a: Set k) (b: Set k):
    Iff (Set.isSubset a b = True) ((key: k) -> Set.contains key a = True -> Set.contains key b = True) :=
  { forward = Set.isSubsetElim a b, backward = Set.isSubsetIntro a b }
