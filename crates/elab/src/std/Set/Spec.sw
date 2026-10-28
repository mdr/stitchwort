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
def Set.present: Option () → Bool
  | Some u => True
  | None => False

theorem Set.containsPresent [auto ord: Ord k] (key: k) (m: Map k ()): Map.contains m key = Set.present (Map.get m key) :=
  match c: Map.get m key with
    | None => rfl
    | Some u => rfl

theorem Set.presentInjective: (x: Option ()) → (y: Option ()) → Set.present x = Set.present y → x = y
  | None, None, h => rfl
  | None, Some w, h => Void.exfalso (Bool.falseNotTrue h)
  | Some u, None, h => Void.exfalso (Bool.trueNotFalse h)
  | Some u, Some w, h => Eq.cong Some (Set.unitEq u w)

theorem Set.ext [auto ord: Ord k]: (s: Set k) → (t: Set k) → ((key: k) → Set.contains s key = Set.contains t key) → s = t
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

theorem Map.getFromKeys [auto ord: Ord k] (ks: Set k) (f: k → v) (key: k):
    Map.get (Map.fromKeys ks f) key = (if Set.contains ks key then Some (f key) else None) :=
  rewrite Map.getMapWithKey ks.items key (key2 u => f key2) in
  match c: Map.get ks.items key with
    | None => rfl
    | Some u => rfl

theorem Map.getRemoveAll [auto ord: Ord k] (m: Map k v) (ks: Set k) (key: k):
    Map.get (Map.removeAll m ks) key = (if Set.contains ks key then None else Map.get m key) :=
  rewrite Map.getFilter m key (key2 value => ¬(Set.contains ks key2)) in
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

theorem Set.lastMapFst: (xs: List (k, ())) → Option.map (List.last xs) Pair.fst = List.last (List.map xs Pair.fst)
  | Nil => rfl
  | Cons e Nil => rfl
  | Cons e (Cons f rest) => Set.lastMapFst (Cons f rest)

-- What `below` finds: a member below `key`, and no member between the two.
theorem Set.belowSome [auto ord: Ord k] (s: Set k) (key: k) (found: k) (h: Set.below s key = Some found):
    And (Set.contains s found = True) (And (found < key) ((other: k) → found < other → other < key → Set.contains s other = False)) :=
  match below: Map.below s.items key with
    | None => Void.exfalso (Option.noneNotSome found h)
    | Some (nearest, unit) =>
      rewrite <- Option.someInjective nearest found h in
      match Map.belowSome s.items key nearest unit below with
        | Both got rest => Both (Map.containsOfGet s.items nearest unit got) rest

-- When `below` finds nothing, no member is below `key`.
theorem Set.belowNone [auto ord: Ord k] (s: Set k) (key: k) (h: Set.below s key = None) (other: k) (less: other < key):
    Set.contains s other = False :=
  match below: Map.below s.items key with
    | None => Map.belowNone s.items key below other less
    | Some (nearest, unit) => Void.exfalso (Option.someNotNone nearest h)

-- What `above` finds: a member above `key`, and no member between the two.
theorem Set.aboveSome [auto ord: Ord k] (s: Set k) (key: k) (found: k) (h: Set.above s key = Some found):
    And (Set.contains s found = True) (And (key < found) ((other: k) → key < other → other < found → Set.contains s other = False)) :=
  match above: Map.above s.items key with
    | None => Void.exfalso (Option.noneNotSome found h)
    | Some (nearest, unit) =>
      rewrite <- Option.someInjective nearest found h in
      match Map.aboveSome s.items key nearest unit above with
        | Both got rest => Both (Map.containsOfGet s.items nearest unit got) rest

-- When `above` finds nothing, no member is above `key`.
theorem Set.aboveNone [auto ord: Ord k] (s: Set k) (key: k) (h: Set.above s key = None) (other: k) (more: key < other):
    Set.contains s other = False :=
  match above: Map.above s.items key with
    | None => Map.aboveNone s.items key above other more
    | Some (nearest, unit) => Void.exfalso (Option.someNotNone nearest h)

theorem Set.containsRemove [auto ord: Ord k] (s: Set k) (key: k): Set.contains (Set.remove s key) key = False :=
  rewrite Map.getRemove s.items key in rfl

theorem Set.containsRemoveOther [auto ord: Ord k] (s: Set k) (key: k) (other: k) (ne: Not (other = key)):
    Set.contains (Set.remove s key) other = Set.contains s other :=
  rewrite Map.getRemoveOther s.items key other ne in rfl

theorem Set.containsUnion [auto ord: Ord k] (a: Set k) (key: k) (b: Set k):
    Set.contains (Set.union a b) key = (Set.contains a key ∨ Set.contains b key) :=
  rewrite Map.getUnion a.items key b.items in
  match c: Map.get a.items key with
    | None => rfl
    | Some u => rfl

theorem Set.containsFilter [auto ord: Ord k] (s: Set k) (key: k) (p: k → Bool):
    Set.contains (Set.filter s p) key = (Set.contains s key ∧ p key) :=
  rewrite Map.getFilter s.items key (key2 u => p key2) in
  match c: Map.get s.items key with
    | None => rfl
    | Some u =>
      match d: p key with
        | True => rfl
        | False => rfl

theorem Set.containsIntersect [auto ord: Ord k] (a: Set k) (key: k) (b: Set k):
    Set.contains (Set.intersect a b) key = (Set.contains a key ∧ Set.contains b key) :=
  rewrite Map.getIntersectWith a.items key b.items (here there => ()) in
  match c: Map.get a.items key with
    | None => rfl
    | Some u =>
      match d: Map.get b.items key with
        | None => rfl
        | Some u2 => rfl

theorem Set.containsDifference [auto ord: Ord k] (a: Set k) (key: k) (b: Set k):
    Set.contains (Set.difference a b) key = (Set.contains a key ∧ ¬(Set.contains b key)) :=
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

-- What a set has, it still has after an insert, and a union has what
-- either side has.
theorem Set.containsInsertMono [auto ord: Ord k] (s: Set k) (key: k) (other: k) (h: Set.contains s other = True):
    Set.contains (Set.insert s key) other = True :=
  match e: other == key with
    | True => rewrite DecEq.sound other key e in Set.containsInsert key s
    | False => rewrite Set.containsInsertOther s key other (DecEq.soundFalse other key e) in h

theorem Set.containsUnionLeft [auto ord: Ord k] (a: Set k) (b: Set k) (key: k) (h: Set.contains a key = True):
    Set.contains (Set.union a b) key = True :=
  rewrite Set.containsUnion a key b, h in rfl

theorem Set.containsUnionRight [auto ord: Ord k] (a: Set k) (b: Set k) (key: k) (h: Set.contains b key = True):
    Set.contains (Set.union a b) key = True :=
  rewrite Set.containsUnion a key b, h in Bool.orTrue (Set.contains a key)

theorem Set.containsInsertMonoExample (s: Set Nat) (h: Set.contains s 2 = True):
    Set.contains (Set.union (Set.insert s 5) (Set.singleton 7)) 2 = True :=
  Set.containsUnionLeft (Set.insert s 5) (Set.singleton 7) 2 (Set.containsInsertMono s 5 2 h)

-- Inserting the list's keys:`key` is there if it was, or if the list has it.
theorem Set.containsFoldInsert [auto ord: Ord k]: (s: Set k) → (key: k) → (xs: List k) →
    Set.contains (List.foldLeft xs s (acc x => Set.insert acc x)) key = (Set.contains s key ∨ List.any xs (x => Map.Spec.sameKey key x))
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
theorem Set.foldAll (q: k → Bool): (z: Bool) → (xs: List (k, ())) →
    Map.Spec.foldLeft (acc key unit => acc ∧ q key) z xs = (z ∧ List.all xs (e => q e.fst))
  | True, Nil => rfl
  | False, Nil => rfl
  | z, Cons (kk, u) rest =>
    rewrite Set.foldAll q (z ∧ q kk) rest in
    match c: z with
      | False => rfl
      | True =>
        match d: q kk with
          | True => rfl
          | False => rfl

theorem Set.allEntriesElim (q: k → Bool) (key: k): (xs: List (k, ())) → List.all xs (e => q e.fst) = True → List.Mem (key, ()) xs → q key = True
  | Nil, h, mem => Void.exfalso mem
  | Cons (kk, u) rest, h, mem =>
    match c: q kk with
      | False => Void.exfalso (Bool.falseNotTrue h)
      | True =>
        match mem with
          | Inl e => Eq.trans (Eq.cong q (Eq.sym (Eq.cong Pair.fst e))) c
          | Inr later => Set.allEntriesElim q key rest h later

theorem Set.allEntriesIntro (q: k → Bool): (xs: List (k, ())) → ((key: k) → List.Mem (key, ()) xs → q key = True) → List.all xs (e => q e.fst) = True
  | Nil, h => rfl
  | Cons (kk, u) rest, h =>
    rewrite h kk (Inl (Eq.cong (w => (kk, w)) (Set.unitEq u ()))) in
    Set.allEntriesIntro q rest (key mem => h key (Inr mem))

theorem Set.isSubsetToList [auto ord: Ord k] (a: Set k) (b: Set k): Set.isSubset a b = List.all (Map.toList a.items) (e => Set.contains b e.fst) :=
  Eq.trans (Map.foldLeftToList (acc key unit => acc ∧ Set.contains b key) True a.items)
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

theorem Set.isSubsetIntro [auto ord: Ord k] (a: Set k) (b: Set k) (h: (key: k) → Set.contains a key = True → Set.contains b key = True):
    Set.isSubset a b = True :=
  Eq.trans (Set.isSubsetToList a b)
    (Set.allEntriesIntro (key2 => Set.contains b key2) (Map.toList a.items) (key mem => h key ((Set.containsToList a key).backward mem)))

-- `isSubset a b` holds exactly when every key of `a` is in `b`.
theorem Set.isSubsetSpec [auto ord: Ord k] (a: Set k) (b: Set k):
    Iff (Set.isSubset a b = True) ((key: k) → Set.contains a key = True → Set.contains b key = True) :=
  { forward = Set.isSubsetElim a b, backward = Set.isSubsetIntro a b }

-- Folds and `map`

theorem Set.foldEntries (f: b → k → b): (entries: List (k, ())) → (initial: b) →
    Map.Spec.foldLeft (acc key unit => f acc key) initial entries = List.foldLeft (List.map entries Pair.fst) initial f
  | Nil, initial => rfl
  | Cons (key, unit) rest, initial => Set.foldEntries f rest (f initial key)

-- A fold over a set is a fold over its keys in order.
theorem Set.foldLeftToList (s: Set k [ord := o]) (initial: b) (f: b → k → b): Set.foldLeft s initial f = List.foldLeft (Set.toList s) initial f :=
  rewrite Map.foldLeftToList (acc key unit => f acc key) initial s.items in Set.foldEntries f (Map.toList s.items) initial

-- A set's list of keys holds what the set holds.
theorem Set.memToList [auto ord: Ord k] (s: Set k) (key: k): Iff (List.Mem key (Set.toList s)) (Set.contains s key = True) := Map.memKeys s.items key

-- Two sets holding the same keys are equal.
theorem Set.extIff [auto ord: Ord k] (s: Set k) (t: Set k) (same: (key: k) → Iff (Set.contains s key = True) (Set.contains t key = True)): s = t :=
  Set.ext s t (key => Bool.eqOf (Set.contains s key) (Set.contains t key) (same key).forward (same key).backward)

-- After an insert, a set holds the key inserted and what it held before.
theorem Set.containsInsertElim [auto ord: Ord k] (s: Set k) (key: k) (other: k) (held: Set.contains (Set.insert s key) other = True):
    Or (other = key) (Set.contains s other = True) :=
  match ord.eq.decide other key with
    | Yes same => Inl same
    | No different => Inr (rewrite Set.containsInsertOther s key other different at held)

-- Removing each of `keys` leaves what the set held and `keys` doesn't.
theorem Set.containsFoldRemove [auto ord: Ord k]: (keys: List k) → (s: Set k) → (key: k) →
    Iff (Set.contains (List.foldLeft keys s Set.remove) key = True) (And (Set.contains s key = True) (Not (List.Mem key keys)))
  | Nil, s, key => { forward = held => Both held (none => none), backward = held => And.left held }
  | Cons first rest, s, key =>
    let later := Set.containsFoldRemove rest (Set.remove s first) key
    {
      forward = held =>
        match later.forward held with
          | Both inRemoved notRest =>
            match ord.eq.decide key first with
              | Yes same => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym inRemoved) (rewrite same in Set.containsRemove s first)))
              | No different =>
                Both (rewrite Set.containsRemoveOther s first key different at inRemoved)
                  (member =>
                    match member with
                      | Inl same => different (Eq.sym same)
                      | Inr inRest => notRest inRest),
      backward = held =>
        let different: Not (key = first) := same => And.right held (Inl (Eq.sym same))
        later.backward (Both (rewrite Set.containsRemoveOther s first key different in And.left held) (inRest => And.right held (Inr inRest)))
    }

-- Inserting `f` of each of `keys` gives what the set held and `f` of each.
theorem Set.containsFoldInsertMap [auto ord: Ord j] (f: k → j): (keys: List k) → (s: Set j) → (key: j) →
    Iff (Set.contains (List.foldLeft keys s (acc x => Set.insert acc (f x))) key = True)
      (Or (Set.contains s key = True) (∃ (x: k) => List.Mem x keys ∧ f x = key))
  | Nil, s, key => {
    forward = held => Inl held,
    backward = held =>
      match held with
        | Inl inSet => inSet
        | Inr (Witness x (Both none same)) => Void.exfalso none
  }
  | Cons first rest, s, key =>
    let later := Set.containsFoldInsertMap f rest (Set.insert s (f first)) key
    {
      forward = held =>
        match later.forward held with
          | Inl inInserted =>
            match Set.containsInsertElim s (f first) key inInserted with
              | Inl same => Inr (Witness first (Both (Inl rfl) (Eq.sym same)))
              | Inr inSet => Inl inSet
          | Inr (Witness x (Both inRest same)) => Inr (Witness x (Both (Inr inRest) same)),
      backward = held =>
        match held with
          | Inl inSet => later.backward (Inl (Set.containsInsertMono s (f first) key inSet))
          | Inr (Witness x (Both (Inl isFirst) same)) => later.backward (Inl (rewrite <- same, <- isFirst in Set.containsInsert (f first) s))
          | Inr (Witness x (Both (Inr inRest) same)) => later.backward (Inr (Witness x (Both inRest same)))
    }

-- `map` holds `f` of each key, and nothing else.
theorem Set.containsMap [auto ordKeys: Ord k] [auto ord: Ord j] (s: Set k) (f: k → j) (key: j):
    Iff (Set.contains (Set.map s f) key = True) (∃ (x: k) => Set.contains s x = True ∧ f x = key) :=
  let folded := Set.containsFoldInsertMap f (Set.toList s) Set.empty key
  {
    forward = held =>
      match folded.forward (rewrite <- Set.foldLeftToList s Set.empty (acc x => Set.insert acc (f x)) in held) with
        | Inl none => Void.exfalso (Bool.falseNotTrue none)
        | Inr (Witness x (Both member same)) => Witness x (Both ((Set.memToList s x).forward member) same),
    backward = held =>
      match held with
        | Witness x (Both inSet same) =>
          rewrite Set.foldLeftToList s Set.empty (acc x => Set.insert acc (f x)) in
            folded.backward (Inr (Witness x (Both ((Set.memToList s x).backward inSet) same)))
  }

theorem Set.mapInsert [auto ordKeys: Ord k] [auto ord: Ord j] (s: Set k) (f: k → j) (key: k):
    Set.map (Set.insert s key) f = Set.insert (Set.map s f) (f key) :=
  Set.extIff (Set.map (Set.insert s key) f) (Set.insert (Set.map s f) (f key)) (other => {
    forward = held =>
      match (Set.containsMap (Set.insert s key) f other).forward held with
        | Witness x (Both inInserted same) =>
          match Set.containsInsertElim s key x inInserted with
            | Inl isKey => rewrite <- same, isKey in Set.containsInsert (f key) (Set.map s f)
            | Inr inSet => Set.containsInsertMono (Set.map s f) (f key) other ((Set.containsMap s f other).backward (Witness x (Both inSet same))),
    backward = held =>
      match Set.containsInsertElim (Set.map s f) (f key) other held with
        | Inl isImage => (Set.containsMap (Set.insert s key) f other).backward (Witness key (Both (Set.containsInsert key s) (Eq.sym isImage)))
        | Inr inImage =>
          match (Set.containsMap s f other).forward inImage with
            | Witness x (Both inSet same) =>
              (Set.containsMap (Set.insert s key) f other).backward (Witness x (Both (Set.containsInsertMono s key x inSet) same))
  })

-- Induction and sizes

-- To prove something of every set, prove it of the empty set, and of a set
-- with a new key inserted, given it of the set before.
theorem Set.induction [auto ord: Ord k] [p: Set k → Prop] (base: p Set.empty)
    (step: (key: k) → (s: Set k) → p s → Set.contains s key = False → p (Set.insert s key)): (s: Set k) → p s
  | { items = m } =>
    Map.induction [p := n => p ({ items = n }: Set k)] base
      (key value n held absent =>
        rewrite Set.unitEq value () in step key ({ items = n }: Set k) held (Eq.trans (Set.containsPresent key n) (Eq.cong Set.present absent)))
      m

theorem Set.sizeEmpty [auto ord: Ord k]: Set.size (Set.empty: Set k) = 0 := rfl

-- Inserting a new key adds one.
theorem Set.sizeInsertNew [auto ord: Ord k] (s: Set k) (key: k) (absent: Set.contains s key = False):
    Set.size (Set.insert s key) = Set.size s + 1 :=
  rewrite Map.sizeInsert s.items key (), absent in rfl

-- Removing a key the set holds takes one away.
theorem Set.sizeRemovePresent [auto ord: Ord k] (s: Set k) (key: k) (present: Set.contains s key = True):
    Set.size (Set.remove s key) = Set.size s - 1 :=
  rewrite Map.sizeRemove s.items key, present in rfl

-- A set holding a key isn't empty.
theorem Set.sizePositive [auto ord: Ord k] (s: Set k) (key: k) (present: Set.contains s key = True): 1 ≤ Set.size s :=
  match c: Set.toList s with
    | Nil => Void.exfalso (rewrite c at ((Set.memToList s key).backward present: List.Mem key (Set.toList s)))
    | Cons first rest => rewrite Set.sizeToList s, c in omega

theorem Set.unionEmpty [auto ord: Ord k] (a: Set k): Set.union a Set.empty = a :=
  Set.ext (Set.union a Set.empty) a (key => rewrite Set.containsUnion a key Set.empty in Bool.orFalse (Set.contains a key))

theorem Set.unionInsert [auto ord: Ord k] (a: Set k) (b: Set k) (key: k): Set.union a (Set.insert b key) = Set.insert (Set.union a b) key :=
  Set.ext (Set.union a (Set.insert b key)) (Set.insert (Set.union a b) key) (other =>
    match ord.eq.decide other key with
      | Yes same =>
        rewrite same, Set.containsUnion a key (Set.insert b key), Set.containsInsert key b, Set.containsInsert key (Set.union a b) in
        Bool.orTrue (Set.contains a key)
      | No different =>
        rewrite Set.containsUnion a other (Set.insert b key), Set.containsInsertOther b key other different,
          Set.containsInsertOther (Set.union a b) key other different, Set.containsUnion a other b in
        rfl)

-- The size of a union of sets with no key in common is the sum of theirs
-- (Mathlib's `Finset.card_disjUnion`).
theorem Set.sizeUnionDisjoint [auto ord: Ord k] (a: Set k) (b: Set k) (disjoint: (key: k) → Set.contains a key = True → Set.contains b key = False):
    Set.size (Set.union a b) = Set.size a + Set.size b :=
  Set.induction [p := t => ((key: k) → Set.contains a key = True → Set.contains t key = False) → Set.size (Set.union a t) = Set.size a + Set.size t]
    (apart => Eq.trans (Eq.cong Set.size (Set.unionEmpty a)) (Eq.sym (Nat.addZero (Set.size a))))
    (key t held absent apart =>
      let apartT := (other: k) (inA: Set.contains a other = True) =>
        Bool.falseOfNotTrue (Set.contains t other)
          (inT => Bool.falseNotTrue (Eq.trans (Eq.sym (apart other inA)) (Set.containsInsertMono t key other inT)))
      let notInA: Set.contains a key = False :=
        Bool.falseOfNotTrue (Set.contains a key) (inA => Bool.falseNotTrue (Eq.trans (Eq.sym (apart key inA)) (Set.containsInsert key t)))
      let newKey: Set.contains (Set.union a t) key = False := rewrite Set.containsUnion a key t, notInA, absent in rfl
      omega [Eq.cong Set.size (Set.unionInsert a t key), Set.sizeInsertNew (Set.union a t) key newKey, Set.sizeInsertNew t key absent, held apartT])
    b disjoint

-- `map` with a function that sends no two keys to the same place keeps the
-- size (Mathlib's `Finset.card_image_of_injective`).
theorem Set.sizeMapInjective [auto ordKeys: Ord k] [auto ord: Ord j] (s: Set k) (f: k → j)
    (injective: (x: k) → (y: k) → Set.contains s x = True → Set.contains s y = True → f x = f y → x = y):
    Set.size (Set.map s f) = Set.size s :=
  Set.induction [p := t => ((x: k) → (y: k) → Set.contains t x = True → Set.contains t y = True → f x = f y → x = y) → Set.size (Set.map t f) = Set.size t]
    (none => rfl)
    (key t held absent injectiveInserted =>
      let injectiveT := (x: k) (y: k) (inX: Set.contains t x = True) (inY: Set.contains t y = True) (same: f x = f y) =>
        injectiveInserted x y (Set.containsInsertMono t key x inX) (Set.containsInsertMono t key y inY) same
      let newImage: Set.contains (Set.map t f) (f key) = False :=
        Bool.falseOfNotTrue (Set.contains (Set.map t f) (f key)) (inImage =>
          match (Set.containsMap t f (f key)).forward inImage with
            | Witness x (Both inT same) =>
              let isKey := injectiveInserted x key (Set.containsInsertMono t key x inT) (Set.containsInsert key t) same
              Bool.falseNotTrue (Eq.trans (Eq.sym absent) (Eq.trans (Eq.sym (Eq.cong (Set.contains t) isKey)) inT)))
      rewrite Set.mapInsert t f key in
      omega [Set.sizeInsertNew (Set.map t f) (f key) newImage, Set.sizeInsertNew t key absent, held injectiveT])
    s injective

theorem Set.differenceEmpty [auto ord: Ord k] (a: Set k): Set.difference a Set.empty = a :=
  Set.ext (Set.difference a Set.empty) a (key =>
    rewrite Set.containsDifference a key Set.empty in
    match c: Set.contains a key with
      | True => rfl
      | False => rfl)

theorem Set.differenceInsert [auto ord: Ord k] (a: Set k) (b: Set k) (key: k):
    Set.difference a (Set.insert b key) = Set.remove (Set.difference a b) key :=
  Set.ext (Set.difference a (Set.insert b key)) (Set.remove (Set.difference a b) key) (other =>
    match ord.eq.decide other key with
      | Yes same =>
        rewrite same, Set.containsDifference a key (Set.insert b key), Set.containsInsert key b, Set.containsRemove (Set.difference a b) key in
        match c: Set.contains a key with
          | True => rfl
          | False => rfl
      | No different =>
        rewrite Set.containsDifference a other (Set.insert b key), Set.containsInsertOther b key other different,
          Set.containsRemoveOther (Set.difference a b) key other different, Set.containsDifference a other b in
        rfl)

-- Taking away a subset leaves the rest (Mathlib's `Finset.card_sdiff`).
theorem Set.sizeDifferenceSubset [auto ord: Ord k] (a: Set k) (b: Set k) (subset: (key: k) → Set.contains b key = True → Set.contains a key = True):
    Set.size (Set.difference a b) + Set.size b = Set.size a :=
  Set.induction [p := t => ((key: k) → Set.contains t key = True → Set.contains a key = True) → Set.size (Set.difference a t) + Set.size t = Set.size a]
    (inside => Eq.trans (Nat.addZero (Set.size (Set.difference a Set.empty))) (Eq.cong Set.size (Set.differenceEmpty a)))
    (key t held absent inside =>
      let insideT := (other: k) (inT: Set.contains t other = True) => inside other (Set.containsInsertMono t key other inT)
      let present: Set.contains (Set.difference a t) key = True :=
        rewrite Set.containsDifference a key t, inside key (Set.containsInsert key t), absent in rfl
      omega [
        Eq.cong Set.size (Set.differenceInsert a t key),
        Set.sizeRemovePresent (Set.difference a t) key present,
        Set.sizePositive (Set.difference a t) key present,
        Set.sizeInsertNew t key absent,
        held insideT
      ])
    b subset

-- A subset is no larger (Mathlib's `Finset.card_le_card`).
theorem Set.sizeSubset [auto ord: Ord k] (a: Set k) (b: Set k) (subset: (key: k) → Set.contains b key = True → Set.contains a key = True):
    Set.size b ≤ Set.size a :=
  omega [Set.sizeDifferenceSubset a b subset]

-- A set holding `count` different keys, `at 0` to `at (count - 1)`, has at
-- least `count` (Mathlib's `Finset.card_le_card_of_injOn`).
theorem Set.countAtMostSize [auto ord: Ord k] (at: Nat → k): (count: Nat) → (s: Set k) →
    ((i: Nat) → i < count → Set.contains s (at i) = True) → ((i: Nat) → (j: Nat) → i < count → j < count → at i = at j → i = j) →
    count ≤ Set.size s
  | Zero, s, members, different => omega
  | Succ count, s, members, different =>
    let rest := Set.remove s (at count)
    let restMembers: (i: Nat) → i < count → Set.contains rest (at i) = True := i below =>
      rewrite Set.containsRemoveOther s (at count) (at i) (same => omega [different i count (omega) (omega) same]) in members i (omega)
    let smaller := Set.countAtMostSize at count rest restMembers (i j below belowJ same => different i j (omega) (omega) same)
    omega [Set.sizeRemovePresent s (at count) (members count (omega)), Set.sizePositive s (at count) (members count (omega))]
