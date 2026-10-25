-- What each set operation does to the keys, from `Map`'s (std/Map/Map.sw),
-- and `Set.ext`: sets with the same keys are equal, whatever order the keys
-- were inserted in (a set's map is a quotient, docs/proposals/
-- map-equality.md §8).

import Std (Eq)

-- What the operations do to the keys in order.

theorem Set.toListInsert [auto ord: Ord k] (s: Set k) (key: k):
    Set.toList (Set.insert s key) = List.map (Map.Spec.insert key () (Map.toList s.items)) Pair.fst :=
  Eq.cong (.map Pair.fst) (Map.toListInsert s.items key ())

theorem Set.toListRemove [auto ord: Ord k] (s: Set k) (key: k):
    Set.toList (Set.remove s key) = List.map (Map.Spec.remove key (Map.toList s.items)) Pair.fst :=
  Eq.cong (.map Pair.fst) (Map.toListRemove s.items key)

theorem Set.sizeToList (s: Set k [ord := o]): Set.size s = List.length (Set.toList s) :=
  Eq.trans (Map.sizeToList s.items) (Eq.sym (List.lengthMap (Map.toList s.items) Pair.fst))

-- `contains` is `get` finding `()`, so the same `contains` everywhere means
-- the same keys.
def Set.present: Option () -> Bool
  | Some u => True
  | None => False

theorem Set.containsPresent [auto ord: Ord k] (key: k) (m: Map k ()): Map.contains m key = Set.present (Map.get m key) :=
  match c: Map.get m key with
    | None => rfl
    | Some u => rfl

theorem Set.presentInjective: (x: Option ()) -> (y: Option ()) -> Set.present x = Set.present y -> x = y
  | None, None, h => rfl
  | None, Some w, h => Void.exfalso (Bool.falseNotTrue h)
  | Some u, None, h => Void.exfalso (Bool.trueNotFalse h)
  | Some u, Some w, h => Eq.cong Some (Set.unitEq u w)

theorem Set.ext [auto ord: Ord k]: (s: Set k) -> (t: Set k) -> ((key: k) -> Set.contains s key = Set.contains t key) -> s = t
  | { items = m }, { items = n }, h =>
    Eq.cong (i => ({ items = i }: Set k))
      (Map.ext m n (key => Set.presentInjective (Map.get m key) (Map.get n key)
        (Eq.trans (Eq.sym (Set.containsPresent key m)) (Eq.trans (h key) (Set.containsPresent key n)))))

-- Maps and sets

theorem Map.containsKeySet [auto ord: Ord k] (m: Map k v) (key: k): Set.contains (Map.keySet m) key = Map.contains m key :=
  rewrite Map.getMap m key (value => ()) in
  match c: Map.get m key with
    | None => rfl
    | Some value => rfl

theorem Map.getFromKeys [auto ord: Ord k] (ks: Set k) (f: k -> v) (key: k):
    Map.get (Map.fromKeys ks f) key = (if Set.contains ks key then Some (f key) else None) :=
  rewrite Map.getMapWithKey ks.items key (key2 u => f key2) in
  match c: Map.get ks.items key with
    | None => rfl
    | Some u => rfl

theorem Map.getRemoveAll [auto ord: Ord k] (m: Map k v) (ks: Set k) (key: k):
    Map.get (Map.removeAll m ks) key = (if Set.contains ks key then None else Map.get m key) :=
  rewrite Map.getFilter m key (key2 value => !(Set.contains ks key2)) in
  match c: Set.contains ks key with
    | True =>
      match d: Map.get m key with
        | None => rfl
        | Some value => rfl
    | False =>
      match d: Map.get m key with
        | None => rfl
        | Some value => rfl

theorem Map.getKeepOnly [auto ord: Ord k] (m: Map k v) (ks: Set k) (key: k):
    Map.get (Map.keepOnly m ks) key = (if Set.contains ks key then Map.get m key else None) :=
  rewrite Map.getFilter m key (key2 value => Set.contains ks key2) in
  match c: Set.contains ks key with
    | True =>
      match d: Map.get m key with
        | None => rfl
        | Some value => rfl
    | False =>
      match d: Map.get m key with
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

theorem Set.lastMapFst: (xs: List (k, ())) -> Option.map (List.last xs) Pair.fst = List.last (List.map xs Pair.fst)
  | Nil => rfl
  | Cons e Nil => rfl
  | Cons e (Cons f rest) => Set.lastMapFst (Cons f rest)

theorem Set.containsRemove [auto ord: Ord k] (s: Set k) (key: k): Set.contains (Set.remove s key) key = False :=
  rewrite Map.getRemove s.items key in rfl

theorem Set.containsRemoveOther [auto ord: Ord k] (s: Set k) (key: k) (other: k) (ne: Not (other = key)):
    Set.contains (Set.remove s key) other = Set.contains s other :=
  rewrite Map.getRemoveOther s.items key other ne in rfl

theorem Set.containsUnion [auto ord: Ord k] (a: Set k) (key: k) (b: Set k):
    Set.contains (Set.union a b) key = (Set.contains a key || Set.contains b key) :=
  rewrite Map.getUnion a.items key b.items in
  match c: Map.get a.items key with
    | None => rfl
    | Some u => rfl

theorem Set.containsFilter [auto ord: Ord k] (s: Set k) (key: k) (p: k -> Bool):
    Set.contains (Set.filter s p) key = (Set.contains s key && p key) :=
  rewrite Map.getFilter s.items key (key2 u => p key2) in
  match c: Map.get s.items key with
    | None => rfl
    | Some u =>
      match d: p key with
        | True => rfl
        | False => rfl

theorem Set.containsIntersect [auto ord: Ord k] (a: Set k) (key: k) (b: Set k):
    Set.contains (Set.intersect a b) key = (Set.contains a key && Set.contains b key) :=
  rewrite Map.getIntersectWith a.items key b.items (here there => ()) in
  match c: Map.get a.items key with
    | None => rfl
    | Some u =>
      match d: Map.get b.items key with
        | None => rfl
        | Some u2 => rfl

theorem Set.containsDifference [auto ord: Ord k] (a: Set k) (key: k) (b: Set k):
    Set.contains (Set.difference a b) key = (Set.contains a key && !(Set.contains b key)) :=
  rewrite Map.getDifference a.items key b.items in
  match c: Map.get a.items key with
    | None => rfl
    | Some u =>
      match d: Map.contains b.items key with
        | True => rfl
        | False => rfl

theorem Set.containsInsertOther [auto ord: Ord k] (s: Set k) (key: k) (other: k) (ne: Not (other = key)):
    Set.contains (Set.insert s key) other = Set.contains s other :=
  rewrite Map.getInsertOther key () other ne s.items in rfl

-- Inserting the list's keys: `key` is there if it was, or if the list has it.
theorem Set.containsFoldInsert [auto ord: Ord k]: (s: Set k) -> (key: k) -> (xs: List k) ->
    Set.contains (List.foldLeft xs s (acc x => Set.insert acc x)) key = (Set.contains s key || List.any xs (x => Map.Spec.sameKey key x))
  | s, key, Nil =>
    match c: Set.contains s key with
      | True => rfl
      | False => rfl
  | s, key, Cons x rest =>
    rewrite Set.containsFoldInsert (Set.insert s x) key rest in
    match e: Ord.compare key x with
      | Equal =>
        rewrite ord.equal key x e, Set.containsInsert x s in
        match c: Set.contains s x with
          | True => rfl
          | False => rfl
      | Less => rewrite Set.containsInsertOther s x key (Map.Spec.notEqualOfCompare key x (z => Ordering.lessNotEqual (Eq.trans (Eq.sym e) z))) in rfl
      | Greater => rewrite Set.containsInsertOther s x key (Map.Spec.notEqualOfCompare key x (z => Ordering.greaterNotEqual (Eq.trans (Eq.sym e) z))) in rfl

theorem Set.containsFromList [auto ord: Ord k] (key: k) (xs: List k): Set.contains (Set.fromList xs) key = List.any xs (x => Map.Spec.sameKey key x) :=
  Set.containsFoldInsert Set.empty key xs

-- `isSubset`: every key of `a` is in `b`

-- `all`'s fold over a set's entries is `List.all` over them.
theorem Set.foldAll (q: k -> Bool): (z: Bool) -> (xs: List (k, ())) ->
    Map.Spec.foldLeft (acc key unit => acc && q key) z xs = (z && List.all xs (e => q e.fst))
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

theorem Set.allEntriesElim (q: k -> Bool) (key: k): (xs: List (k, ())) -> List.all xs (e => q e.fst) = True -> List.Mem (key, ()) xs -> q key = True
  | Nil, h, mem => Void.exfalso mem
  | Cons (kk, u) rest, h, mem =>
    match c: q kk with
      | False => Void.exfalso (Bool.falseNotTrue h)
      | True =>
        match mem with
          | Inl e => Eq.trans (Eq.cong q (Eq.sym (Eq.cong Pair.fst e))) c
          | Inr later => Set.allEntriesElim q key rest h later

theorem Set.allEntriesIntro (q: k -> Bool): (xs: List (k, ())) -> ((key: k) -> List.Mem (key, ()) xs -> q key = True) -> List.all xs (e => q e.fst) = True
  | Nil, h => rfl
  | Cons (kk, u) rest, h =>
    rewrite h kk (Inl (Eq.cong (w => (kk, w)) (Set.unitEq u ()))) in
    Set.allEntriesIntro q rest (key mem => h key (Inr mem))

theorem Set.isSubsetToList [auto ord: Ord k] (a: Set k) (b: Set k): Set.isSubset a b = List.all (Map.toList a.items) (e => Set.contains b e.fst) :=
  Eq.trans (Map.foldLeftToList (acc key unit => acc && Set.contains b key) True a.items)
    (Set.foldAll (key => Set.contains b key) True (Map.toList a.items))

-- A set has `key` exactly when its map's entries have `(key, ())`.
theorem Set.containsToList [auto ord: Ord k] (s: Set k) (key: k): Iff (Set.contains s key = True) (List.Mem (key, ()) (Map.toList s.items)) := {
  forward = h =>
    match c: Map.get s.items key with
      | None => Void.exfalso (Bool.falseNotTrue h)
      | Some u => (Map.memToList s.items key ()).backward (Eq.trans c (Eq.cong Some (Set.unitEq u ()))),
  backward = mem => rewrite (Map.memToList s.items key ()).forward mem in rfl
}

theorem Set.isSubsetElim [auto ord: Ord k] (a: Set k) (b: Set k) (h: Set.isSubset a b = True) (key: k) (inA: Set.contains a key = True):
    Set.contains b key = True :=
  Set.allEntriesElim (key2 => Set.contains b key2) key (Map.toList a.items) (Eq.trans (Eq.sym (Set.isSubsetToList a b)) h)
    ((Set.containsToList a key).forward inA)

theorem Set.isSubsetIntro [auto ord: Ord k] (a: Set k) (b: Set k) (h: (key: k) -> Set.contains a key = True -> Set.contains b key = True):
    Set.isSubset a b = True :=
  Eq.trans (Set.isSubsetToList a b)
    (Set.allEntriesIntro (key2 => Set.contains b key2) (Map.toList a.items) (key mem => h key ((Set.containsToList a key).backward mem)))

-- `isSubset a b` holds exactly when every key of `a` is in `b`.
theorem Set.isSubsetSpec [auto ord: Ord k] (a: Set k) (b: Set k):
    Iff (Set.isSubset a b = True) ((key: k) -> Set.contains a key = True -> Set.contains b key = True) :=
  { forward = Set.isSubsetElim a b, backward = Set.isSubsetIntro a b }
