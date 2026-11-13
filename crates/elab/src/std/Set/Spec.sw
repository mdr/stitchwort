--| What each set operation does to the keys, from `Map`'s (std/Map/Map.sw),
--| and [`Set.ext`]: sets with the same keys are equal, whatever order the keys
--| were inserted in (a set's map is a quotient).
-- (docs/proposals/map-equality.md §8)

import Std (Eq)

--| What the operations do to the keys in order.

theorem Set.toListInsert [auto ord: Ord k] (s: Set k) (key: k):
    Set.toList (Set.insert s key) = List.map (Map.Spec.insert key () (Map.toList s.items)) Pair.fst :=
  Eq.cong (.map Pair.fst) (Map.toListInsert s.items key ())

theorem Set.toListRemove [auto ord: Ord k] (s: Set k) (key: k):
    Set.toList (Set.remove s key) = List.map (Map.Spec.remove key (Map.toList s.items)) Pair.fst :=
  Eq.cong (.map Pair.fst) (Map.toListRemove s.items key)

theorem Set.sizeToList (s: Set k [ord := o]): Set.size s = List.length (Set.toList s) :=
  Eq.trans (Map.sizeToList s.items) (Eq.sym (List.lengthMap (Map.toList s.items) Pair.fst))

--| Whether an option has a value: how `Set.contains` reads what `Map.get` finds.
-- `contains` is `get` finding `()`, so the same `contains` everywhere means
-- the same keys.
def Set.present: (option: Option ()) → Bool
  | Some u => True
  | None => False

theorem Set.containsPresent [auto ord: Ord k] (key: k) (m: Map k ()): Map.contains m key = Set.present (Map.get m key) :=
  match c: Map.get m key with
    | None => rfl
    | Some u => rfl

theorem Set.presentInjective (x y: Option ()) (h: Set.present x = Set.present y): x = y :=
  match x, y with
    | None, None => rfl
    | Some u, Some w => Eq.cong Some (Set.unitEq u w)

theorem Set.ext [auto ord: Ord k] (s t: Set k) (h: (∀ (key: k) => Set.contains s key = Set.contains t key)): s = t :=
  match s, t with
    | { items = m }, { items = n } =>
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
    | [] => rfl
    | [e, ..rest] => rfl

theorem Set.maxToList (s: Set k [ord := o]): Set.max s = List.last (Set.toList s) :=
  rewrite Map.maxToList s.items in Set.lastMapFst (Map.toList s.items)

--| The smallest key is in the set.
theorem Set.containsMin [auto ord: Ord k] (s: Set k) (least: k) (found: Set.min s = Some least): Set.contains s least = True :=
  match entries: Map.toList s.items with
    | [] => Void.exfalso (Option.someNotNone least (Eq.trans (Eq.sym found) (rewrite Map.minToList s.items, entries in rfl)))
    | [entry, ..rest] =>
      let first: Set.min s = Some entry.fst := rewrite Map.minToList s.items, entries in rfl
      Map.containsOfMemToList s.items least entry (rewrite entries in Inl rfl) (Option.someInjective (Eq.trans (Eq.sym first) found))

--| The smallest key is at most every key of the set.
theorem Set.minLeast [auto ord: Ord k] (s: Set k) (least: k) (found: Set.min s = Some least) (key: k) (there: Set.contains s key = True): least <= key :=
  match entries: Map.toList s.items with
    | [] => Void.exfalso (Option.someNotNone least (Eq.trans (Eq.sym found) (rewrite Map.minToList s.items, entries in rfl)))
    | [(first, unit), ..rest] =>
      let isMin: Set.min s = Some first := rewrite Map.minToList s.items, entries in rfl
      let same: first = least := Option.someInjective (Eq.trans (Eq.sym isMin) found)
      let member := Map.memKeysOfContains s.items key there
      rewrite entries at member in
        match member with
          | Inl here => rewrite <- same, <- here in Ord.leRefl first
          | Inr later =>
            let sorted := Map.toListSorted s.items
            rewrite entries at sorted in
              let (Both bottom ascending) := sorted
              let above := Map.Spec.keysAbove ord key (Some first) rest ascending later
              rewrite <- same in Ord.lessLe first key (ord.lessThanOf first key above)

--| A set holding a key has a smallest one.
theorem Set.minOfContains [auto ord: Ord k] (s: Set k) (key: k) (there: Set.contains s key = True): ∃ (least: k) => Set.min s = Some least :=
  match least: Set.min s with
    | Some smallest => Witness smallest rfl
    | None => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Set.missingOfMinNone s least key)) there))

--| `popMin` is `min` and `remove` together.
theorem Set.popMinSpec [auto ord: Ord k] (s: Set k): Set.popMin s = Option.map (Set.min s) (key => (key, Set.remove s key)) :=
  rewrite Map.popMinSpec s.items in
  match Map.min s.items with
    | None => rfl
    | Some entry => rfl

--| What `popMin` finds: the smallest key, and the set without it.
theorem Set.popMinSome [auto ord: Ord k] (s: Set k) (key: k) (rest: Set k) (found: Set.popMin s = Some (key, rest)):
    (Set.min s = Some key) ∧ (rest = Set.remove s key) :=
  let spec := Set.popMinSpec s
  match least: Set.min s with
    | None => Void.exfalso (Option.noneNotSome (key, rest) (Eq.trans (Eq.sym spec) found))
    | Some smallest =>
      let pairs: (smallest, Set.remove s smallest) = (key, rest) := Option.someInjective (Eq.trans (Eq.sym spec) found)
      rewrite <- Eq.cong Pair.fst pairs, <- Eq.cong Pair.snd pairs in Both rfl rfl

--| `popMin` finds nothing only in an empty set.
theorem Set.popMinNone [auto ord: Ord k] (s: Set k) (found: Set.popMin s = None): Set.min s = None :=
  let spec := Set.popMinSpec s
  match least: Set.min s with
    | None => rfl
    | Some smallest => Void.exfalso (Option.someNotNone _ (Eq.trans (Eq.sym spec) found))

--| What `popMin` leaves is one smaller.
theorem Set.sizePopMin [auto ord: Ord k] (s: Set k) (key: k) (rest: Set k) (found: Set.popMin s = Some (key, rest)):
    Set.size rest < Set.size s :=
  let (Both least restIs) := Set.popMinSome s key rest found
  let present := Set.containsMin s key least
  rewrite restIs, Set.sizeRemovePresent s key present in omega [Set.sizePositive s key present]

--| A set with no smallest key holds nothing.
theorem Set.missingOfMinNone [auto ord: Ord k] (s: Set k) (empty: Set.min s = None) (key: k): Set.contains s key = False :=
  match there: Set.contains s key with
    | False => rfl
    | True =>
      let member := Map.memKeysOfContains s.items key there
      match entries: Map.toList s.items with
        | [entry, ..rest] =>
          let first: Set.min s = Some entry.fst := rewrite Map.minToList s.items, entries in rfl
          Void.exfalso (Option.someNotNone entry.fst (Eq.trans (Eq.sym first) empty))

--| What's left after removing a key was there before.
theorem Set.containsOfRemove [auto ord: Ord k] (s: Set k) (key: k) (other: k) (there: Set.contains (Set.remove s key) other = True):
    Set.contains s other = True :=
  match same: other == key with
    | True =>
      let moved := Eq.cong (found => Set.contains (Set.remove s key) found) (Eq.sym same.read)
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Set.containsRemove s key)) (Eq.trans moved there)))
    | False => Eq.trans (Eq.sym (Set.containsRemoveOther s key other same.read)) there

theorem Set.lastMapFst (xs: List (k, ())): Option.map (List.last xs) Pair.fst = List.last (List.map xs Pair.fst) :=
  match xs with
    | [] => rfl
    | [e] => rfl
    | [e, f, ..rest] => Set.lastMapFst [f, ..rest]

--| What `below` finds: a member below `key`, and no member between the two.
theorem Set.belowSome [auto ord: Ord k] (s: Set k) (key: k) (found: k) (h: Set.below s key = Some found):
    (Set.contains s found = True) ∧ ((found < key) ∧ (∀ (other: k) => found < other → other < key → Set.contains s other = False)) :=
  match below: Map.below s.items key with
    | Some (nearest, unit) =>
      rewrite <- Option.someInjective h in
      match Map.belowSome s.items key nearest unit below with
        | Both got rest => Both (Map.containsOfGet s.items nearest unit got) rest

--| When `below` finds nothing, no member is below `key`.
theorem Set.belowNone [auto ord: Ord k] (s: Set k) (key: k) (h: Set.below s key = None) (other: k) (less: other < key):
    Set.contains s other = False :=
  match below: Map.below s.items key with
    | None => Map.belowNone s.items key below other less

--| What `above` finds: a member above `key`, and no member between the two.
theorem Set.aboveSome [auto ord: Ord k] (s: Set k) (key: k) (found: k) (h: Set.above s key = Some found):
    (Set.contains s found = True) ∧ ((key < found) ∧ (∀ (other: k) => key < other → other < found → Set.contains s other = False)) :=
  match above: Map.above s.items key with
    | Some (nearest, unit) =>
      rewrite <- Option.someInjective h in
      match Map.aboveSome s.items key nearest unit above with
        | Both got rest => Both (Map.containsOfGet s.items nearest unit got) rest

--| When `above` finds nothing, no member is above `key`.
theorem Set.aboveNone [auto ord: Ord k] (s: Set k) (key: k) (h: Set.above s key = None) (other: k) (more: key < other):
    Set.contains s other = False :=
  match above: Map.above s.items key with
    | None => Map.aboveNone s.items key above other more

theorem Set.containsRemove [auto ord: Ord k] (s: Set k) (key: k): Set.contains (Set.remove s key) key = False :=
  rewrite Map.getRemove s.items key in rfl

theorem Set.containsRemoveOther [auto ord: Ord k] (s: Set k) (key: k) (other: k) (ne: other ≠ key):
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

theorem Set.containsInsertOther [auto ord: Ord k] (s: Set k) (key: k) (other: k) (ne: other ≠ key):
    Set.contains (Set.insert s key) other = Set.contains s other :=
  rewrite Map.getInsertOther key () other ne s.items in rfl

-- What a set has, it still has after an insert, and a union has what
-- either side has.

--| What a set has, it still has after an insert.
theorem Set.containsInsertMono [auto ord: Ord k] (s: Set k) (key: k) (other: k) (h: Set.contains s other = True):
    Set.contains (Set.insert s key) other = True :=
  match e: other == key with
    | True => rewrite e.read in Set.containsInsert key s
    | False => rewrite Set.containsInsertOther s key other e.read in h

--| A union has what its first set has.
theorem Set.containsUnionLeft [auto ord: Ord k] (a: Set k) (b: Set k) (key: k) (h: Set.contains a key = True):
    Set.contains (Set.union a b) key = True :=
  rewrite Set.containsUnion a key b, h in rfl

--| A union has what its second set has.
theorem Set.containsUnionRight [auto ord: Ord k] (a: Set k) (b: Set k) (key: k) (h: Set.contains b key = True):
    Set.contains (Set.union a b) key = True :=
  rewrite Set.containsUnion a key b, h in Bool.orTrue (Set.contains a key)

theorem Set.containsInsertMonoExample (s: Set Nat) (h: Set.contains s 2 = True):
    Set.contains (Set.union (Set.insert s 5) (Set.singleton 7)) 2 = True :=
  Set.containsUnionLeft (Set.insert s 5) (Set.singleton 7) 2 (Set.containsInsertMono s 5 2 h)

--| Inserting the list's keys:`key` is there if it was, or if the list has it.
theorem Set.containsFoldInsert [auto ord: Ord k] (s: Set k) (key: k) (xs: List k):
    Set.contains (List.foldLeft xs s (acc x => Set.insert acc x)) key = (Set.contains s key ∨ List.any xs (x => Map.Spec.sameKey key x)) :=
  match xs with
    | [] =>
      match c: Set.contains s key with
        | True => rfl
        | False => rfl
    | [x, ..rest] =>
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

--| `contains` on a set built from a list is membership.
theorem Set.containsFromListIff [auto ord: Ord k] (xs: List k) (key: k): (Set.contains (Set.fromList xs) key = True) ↔ (key ∈ xs) := {
  forward = there =>
    let found: xs.any (x => Map.Spec.sameKey key x) := rewrite Set.containsFromList key xs at there in there
    let Witness x (Both member same) := found
    rewrite Map.Spec.sameKeySound key x same in member,
  backward = member =>
    rewrite Set.containsFromList key xs in
      Witness key (Both member (rewrite Map.Spec.sameKeyDecide key key in DecEq.refl key))
}

-- `isSubset`: every key of `a` is in `b`

--| `all`'s fold over a set's entries is `List.all` over them.
theorem Set.foldAll (q: k → Bool) (z: Bool) (xs: List (k, ())):
    Map.Spec.foldLeft (acc key unit => acc ∧ q key) z xs = (z ∧ List.all xs (e => q e.fst)) :=
  match z, xs with
    | True, [] => rfl
    | False, [] => rfl
    | z, [(kk, u), ..rest] =>
      rewrite Set.foldAll q (z ∧ q kk) rest in
      rfl

theorem Set.allEntriesElim (q: k → Bool) (key: k) (xs: List (k, ())) (h: List.all xs (e => q e.fst) = True) (mem: List.Mem (key, ()) xs): q key = True :=
  match xs with
    | [(kk, u), ..rest] =>
      match c: q kk with
        | True =>
          match mem with
            | Inl e => Eq.trans (Eq.cong q (Eq.sym (Eq.cong Pair.fst e))) c
            | Inr later => Set.allEntriesElim q key rest h later

theorem Set.allEntriesIntro (q: k → Bool) (xs: List (k, ())) (h: (∀ (key: k) => List.Mem (key, ()) xs → q key = True)): List.all xs (e => q e.fst) = True :=
  match xs with
    | [] => rfl
    | [(kk, u), ..rest] =>
      rewrite h kk (Inl (Eq.cong (w => (kk, w)) (Set.unitEq u ()))) in
      Set.allEntriesIntro q rest (key mem => h key (Inr mem))

--| Whether every key of `a` is in `b` ([`Set.isSubsetReads`]). It is declared here, beside its reading, which needs the lemmas below.
def Set.isSubset [auto ord: Ord k] (a: Set k) (b: Set k): Bool := Set.all a (key => Set.contains b key)

theorem Set.isSubsetToList [auto ord: Ord k] (a: Set k) (b: Set k): Set.isSubset a b = List.all (Map.toList a.items) (e => Set.contains b e.fst) :=
  Eq.trans (Map.foldLeftToList (acc key unit => acc ∧ Set.contains b key) True a.items)
    (Set.foldAll (key => Set.contains b key) True (Map.toList a.items))

--| A set has `key` exactly when its map's entries have `(key, ())`.
theorem Set.containsToList [auto ord: Ord k] (s: Set k) (key: k): (Set.contains s key = True) ↔ (List.Mem (key, ()) (Map.toList s.items)) := {
  forward = h =>
    match c: Map.get s.items key with
      | Some u => (Map.memToList s.items key ()).backward (Eq.trans c (Eq.cong Some (Set.unitEq u ()))),
  backward = mem => rewrite (Map.memToList s.items key ()).forward mem in rfl
}

theorem Set.isSubsetElim [auto ord: Ord k] (a: Set k) (b: Set k) (h: Set.isSubset a b = True) (key: k) (inA: Set.contains a key = True):
    Set.contains b key = True :=
  Set.allEntriesElim (key2 => Set.contains b key2) key (Map.toList a.items) (Eq.trans (Eq.sym (Set.isSubsetToList a b)) h)
    ((Set.containsToList a key).forward inA)

theorem Set.isSubsetIntro [auto ord: Ord k] [a: Set k] [b: Set k] (h: ∀ (key: k) => Set.contains a key = True → Set.contains b key = True):
    Set.isSubset a b = True :=
  Eq.trans (Set.isSubsetToList a b)
    (Set.allEntriesIntro (key2 => Set.contains b key2) (Map.toList a.items) (key mem => h key ((Set.containsToList a key).backward mem)))

test "set: isSubset" :=
  Set.isSubset (Set.fromList [1, 2]) Set.example ∧ ¬(Set.isSubset (Set.fromList [1, 4]) Set.example)
test "set: isSubset, edge cases" :=
  Set.isSubset Set.empty Set.example ∧ Set.isSubset Set.example Set.example ∧ ¬(Set.isSubset Set.example Set.empty)

--| `a.isSubset b` reads as "every key of `a` is in `b`".
@[reading]
theorem Set.isSubsetReads [auto ord: Ord k] (a: Set k) (b: Set k):
    Set.isSubset a b ↔ ∀ (key: k) => key ∈ a → key ∈ b :=
  { forward = Set.isSubsetElim a b, backward = Set.isSubsetIntro }

-- Folds and `map`

theorem Set.foldEntries (f: b → k → b) (entries: List (k, ())) (initial: b):
    Map.Spec.foldLeft (acc key unit => f acc key) initial entries = List.foldLeft (List.map entries Pair.fst) initial f :=
  match entries with
    | [] => rfl
    | [(key, unit), ..rest] => Set.foldEntries f rest (f initial key)

--| A fold over a set is a fold over its keys in order.
theorem Set.foldLeftToList (s: Set k [ord := o]) (initial: b) (f: b → k → b): Set.foldLeft s initial f = List.foldLeft (Set.toList s) initial f :=
  rewrite Map.foldLeftToList (acc key unit => f acc key) initial s.items in Set.foldEntries f (Map.toList s.items) initial

--| Counting in a set counts in its list of keys.
theorem Set.countToList (s: Set k [ord := o]) (p: k → Bool): Set.count s p = List.count (Set.toList s) p :=
  Set.foldLeftToList s 0 (n key => Nat.succIf n (p key))

--| A set's list of keys holds what the set holds.
theorem Set.memToList [auto ord: Ord k] (s: Set k) (key: k): (List.Mem key (Set.toList s)) ↔ (Set.contains s key = True) := Map.memKeys s.items key

--| Two sets holding the same keys are equal.
theorem Set.extIff [auto ord: Ord k] (s: Set k) (t: Set k) (same: ∀ (key: k) => (Set.contains s key = True) ↔ (Set.contains t key = True)): s = t :=
  Set.ext s t (key => Bool.eqOf (Set.contains s key) (Set.contains t key) (same key).forward (same key).backward)

--| After an insert, a set holds the key inserted and what it held before.
theorem Set.containsInsertElim [auto ord: Ord k] (s: Set k) (key: k) (other: k) (held: Set.contains (Set.insert s key) other = True):
    (other = key) ∨ (Set.contains s other = True) :=
  if same: other = key then Inl same
  else Inr (rewrite Set.containsInsertOther s key other same at held)

-- The facts above as `Iff`s, for a proof that goes from membership in one
-- direction or the other: each says what holding the key means for the sets
-- the operation was made from.

--| After an insert, a set holds exactly the key inserted and what it held before.
theorem Set.containsInsertIff [auto ord: Ord k] (s: Set k) (key: k) (other: k):
    (Set.contains (Set.insert s key) other = True) ↔ ((other = key) ∨ (Set.contains s other = True)) := {
  forward = Set.containsInsertElim s key other,
  backward = either =>
    match either with
      | Inl same => rewrite same in Set.containsInsert key s
      | Inr held => Set.containsInsertMono s key other held
}

--| A union holds exactly what either set holds.
theorem Set.containsUnionIff [auto ord: Ord k] (a: Set k) (key: k) (b: Set k):
    (Set.contains (Set.union a b) key = True) ↔ ((Set.contains a key = True) ∨ (Set.contains b key = True)) := {
  forward = h =>
    (rewrite Set.containsUnion a key b at h in h).read,
  backward = either =>
    rewrite Set.containsUnion a key b in
    match either with
      | Inl inA => Inl inA
      | Inr inB => Inr inB
}

--| An intersection holds exactly what both sets hold.
theorem Set.containsIntersectIff [auto ord: Ord k] (a: Set k) (key: k) (b: Set k):
    (Set.contains (Set.intersect a b) key = True) ↔ ((Set.contains a key = True) ∧ (Set.contains b key = True)) := {
  forward = h =>
    (rewrite Set.containsIntersect a key b at h in h).read,
  backward = (Both inA inB) => rewrite Set.containsIntersect a key b in Both inA inB
}

--| A difference `a` minus `b` holds exactly what `a` holds and `b` doesn't.
theorem Set.containsDifferenceIff [auto ord: Ord k] (a: Set k) (key: k) (b: Set k):
    (Set.contains (Set.difference a b) key = True) ↔ ((Set.contains a key = True) ∧ (Set.contains b key = False)) := {
  forward = h =>
    let Both inA outB := rewrite Set.containsDifference a key b at h in h
    Both inA outB.read,
  backward = (Both inA outB) => rewrite Set.containsDifference a key b in Both inA (Bool.notOfFalse _ outB)
}

--| A filtered set holds exactly the keys of the set that pass the test.
theorem Set.containsFilterIff [auto ord: Ord k] (s: Set k) (key: k) (p: k → Bool):
    (Set.contains (Set.filter s p) key = True) ↔ ((Set.contains s key = True) ∧ (p key = True)) := {
  forward = h =>
    (rewrite Set.containsFilter s key p at h in h).read,
  backward = (Both inS kept) => rewrite Set.containsFilter s key p in Both inS kept
}

--| Removing each of `keys` leaves what the set held and `keys` doesn't.
theorem Set.containsFoldRemove [auto ord: Ord k] (keys: List k) (s: Set k) (key: k):
    (Set.contains (List.foldLeft keys s Set.remove) key = True) ↔ ((Set.contains s key = True) ∧ (¬(List.Mem key keys))) :=
  match keys with
    | [] => { forward = held => Both held (none => none), backward = held => And.left held }
    | [first, ..rest] =>
      let later := Set.containsFoldRemove rest (Set.remove s first) key
      {
        forward = held =>
          match later.forward held with
            | Both inRemoved notRest =>
              if same: key = first then Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym inRemoved) (rewrite same in Set.containsRemove s first)))
              else
                Both (rewrite Set.containsRemoveOther s first key same at inRemoved)
                  (member =>
                    match member with
                      | Inl equal => same (Eq.sym equal)
                      | Inr inRest => notRest inRest),
        backward = held =>
          let different: key ≠ first := same => And.right held (Inl (Eq.sym same))
          later.backward (Both (rewrite Set.containsRemoveOther s first key different in And.left held) (inRest => And.right held (Inr inRest)))
      }

--| Inserting `f` of each of `keys` gives what the set held and `f` of each.
theorem Set.containsFoldInsertMap [auto ord: Ord j] (f: k → j) (keys: List k) (s: Set j) (key: j):
    (Set.contains (List.foldLeft keys s (acc x => Set.insert acc (f x))) key = True) ↔ ((Set.contains s key = True) ∨ (∃ (x: k) => List.Mem x keys ∧ f x = key)) :=
  match keys with
    | [] => {
      forward = held => Inl held,
      backward = held =>
        match held with
          | Inl inSet => inSet
          | Inr (Witness x (Both none same)) => Void.exfalso none
    }
    | [first, ..rest] =>
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

--| `map` holds `f` of each key, and nothing else.
theorem Set.containsMap [auto ordKeys: Ord k] [auto ord: Ord j] (s: Set k) (f: k → j) (key: j):
    (Set.contains (Set.map s f) key = True) ↔ (∃ (x: k) => Set.contains s x = True ∧ f x = key) :=
  let folded := Set.containsFoldInsertMap f (Set.toList s) Set.empty key
  {
    forward = held =>
      match folded.forward (rewrite <- Set.foldLeftToList s Set.empty (acc x => Set.insert acc (f x)) in held) with
        | Inl none => cases
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

--| To prove something of every set, prove it of the empty set, and of a set
--| with a new key inserted, given it of the set before.
theorem Set.induction [auto ord: Ord k] [p: Set k → Prop] (base: p Set.empty)
    (step: ∀ (key: k) (s: Set k) => p s → Set.contains s key = False → p (Set.insert s key)) (s: Set k): p s :=
  match s with
    | { items = m } =>
      Map.induction [p := n => p ({ items = n }: Set k)] base
        (key value n held absent =>
          rewrite Set.unitEq value () in step key ({ items = n }: Set k) held (Eq.trans (Set.containsPresent key n) (Eq.cong Set.present absent)))
        m

theorem Set.sizeEmpty [auto ord: Ord k]: Set.size (Set.empty: Set k) = 0 := rfl

--| Inserting a new key adds one.
theorem Set.sizeInsertNew [auto ord: Ord k] (s: Set k) (key: k) (absent: Set.contains s key = False):
    Set.size (Set.insert s key) = Set.size s + 1 :=
  rewrite Map.sizeInsert s.items key (), absent in rfl

--| Removing a key the set holds takes one away.
theorem Set.sizeRemovePresent [auto ord: Ord k] (s: Set k) (key: k) (present: Set.contains s key = True):
    Set.size (Set.remove s key) = Set.size s - 1 :=
  rewrite Map.sizeRemove s.items key, present in rfl

--| A set holding a key isn't empty.
theorem Set.sizePositive [auto ord: Ord k] (s: Set k) (key: k) (present: Set.contains s key = True): 1 ≤ Set.size s :=
  match c: Set.toList s with
    | [] => Void.exfalso (rewrite c at ((Set.memToList s key).backward present: List.Mem key (Set.toList s)))
    | [first, ..rest] => rewrite Set.sizeToList s, c in omega

theorem Set.unionEmpty [auto ord: Ord k] (a: Set k): Set.union a Set.empty = a :=
  Set.ext (Set.union a Set.empty) a (key => rewrite Set.containsUnion a key Set.empty in Bool.orFalse (Set.contains a key))

theorem Set.unionInsert [auto ord: Ord k] (a: Set k) (b: Set k) (key: k): Set.union a (Set.insert b key) = Set.insert (Set.union a b) key :=
  Set.ext (Set.union a (Set.insert b key)) (Set.insert (Set.union a b) key) (other =>
    if same: other = key then
      rewrite same, Set.containsUnion a key (Set.insert b key), Set.containsInsert key b, Set.containsInsert key (Set.union a b) in
      Bool.orTrue (Set.contains a key)
    else
      rewrite Set.containsUnion a other (Set.insert b key), Set.containsInsertOther b key other same,
        Set.containsInsertOther (Set.union a b) key other same, Set.containsUnion a other b in
      rfl)

--| The size of a union of sets with no key in common is the sum of theirs
--| (Mathlib's `Finset.card_disjUnion`).
theorem Set.sizeUnionDisjoint [auto ord: Ord k] (a: Set k) (b: Set k) (disjoint: ∀ (key: k) => Set.contains a key = True → Set.contains b key = False):
    Set.size (Set.union a b) = Set.size a + Set.size b :=
  Set.induction [p := t => (∀ (key: k) => Set.contains a key = True → Set.contains t key = False) → Set.size (Set.union a t) = Set.size a + Set.size t]
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

--| `map` with a function that sends no two keys to the same place keeps the
--| size (Mathlib's `Finset.card_image_of_injective`).
theorem Set.sizeMapInjective [auto ordKeys: Ord k] [auto ord: Ord j] (s: Set k) (f: k → j)
    (injective: ∀ (x y: k) => Set.contains s x = True → Set.contains s y = True → f x = f y → x = y):
    Set.size (Set.map s f) = Set.size s :=
  Set.induction [p := t => (∀ (x y: k) => Set.contains t x = True → Set.contains t y = True → f x = f y → x = y) → Set.size (Set.map t f) = Set.size t]
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
    if same: other = key then
      rewrite same, Set.containsDifference a key (Set.insert b key), Set.containsInsert key b, Set.containsRemove (Set.difference a b) key in
      match c: Set.contains a key with
        | True => rfl
        | False => rfl
    else
      rewrite Set.containsDifference a other (Set.insert b key), Set.containsInsertOther b key other same,
        Set.containsRemoveOther (Set.difference a b) key other same, Set.containsDifference a other b in
      rfl)

--| Taking away a subset leaves the rest (Mathlib's `Finset.card_sdiff`).
theorem Set.sizeDifferenceSubset [auto ord: Ord k] (a: Set k) (b: Set k) (subset: ∀ (key: k) => Set.contains b key = True → Set.contains a key = True):
    Set.size (Set.difference a b) + Set.size b = Set.size a :=
  Set.induction [p := t => (∀ (key: k) => Set.contains t key = True → Set.contains a key = True) → Set.size (Set.difference a t) + Set.size t = Set.size a]
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

--| A subset is no larger (Mathlib's `Finset.card_le_card`).
theorem Set.sizeSubset [auto ord: Ord k] (a: Set k) (b: Set k) (subset: ∀ (key: k) => Set.contains b key = True → Set.contains a key = True):
    Set.size b ≤ Set.size a :=
  omega [Set.sizeDifferenceSubset a b subset]

--| An intersection is no larger than either side (Mathlib's
--| `Finset.card_inter_le_left` and `card_inter_le_right`).
theorem Set.sizeIntersectLeft [auto ord: Ord k] (a: Set k) (b: Set k): Set.size (Set.intersect a b) ≤ Set.size a :=
  Set.sizeSubset a (Set.intersect a b) (key held =>
    rewrite Set.containsIntersect a key b at held in held.left)

theorem Set.sizeIntersectRight [auto ord: Ord k] (a: Set k) (b: Set k): Set.size (Set.intersect a b) ≤ Set.size b :=
  Set.sizeSubset b (Set.intersect a b) (key held =>
    rewrite Set.containsIntersect a key b at held in held.right)

--| A set holding `count` different keys, `at 0` to `at (count - 1)`, has at
--| least `count` (Mathlib's `Finset.card_le_card_of_injOn`).
theorem Set.countAtMostSize [auto ord: Ord k] (at: Nat → k) (count: Nat) (s: Set k)
    (members: (∀ (i: Nat) => i < count → Set.contains s (at i) = True)) (different: (∀ (i j: Nat) => i < count → j < count → at i = at j → i = j)):
    count ≤ Set.size s :=
  match count with
    | Zero => omega
    | Succ count =>
      let rest := Set.remove s (at count)
      let restMembers: ∀ (i: Nat) => i < count → Set.contains rest (at i) = True := i below =>
        rewrite Set.containsRemoveOther s (at count) (at i) (same => omega [different i count (omega) (omega) same]) in members i (omega)
      let smaller := Set.countAtMostSize at count rest restMembers (i j below belowJ same => different i j (omega) (omega) same)
      omega [Set.sizeRemovePresent s (at count) (members count (omega)), Set.sizePositive s (at count) (members count (omega))]

--| Folding a list of sets into `acc` by union holds what `acc` holds or some
--| set in the list does.
theorem Set.containsFoldUnion [auto ord: Ord k] (key: k) (ss: List (Set k)) (acc: Set k):
    Set.contains (List.foldLeft ss acc Set.union) key = (Set.contains acc key ∨ List.any ss (s => Set.contains s key)) :=
  match ss with
    | [] => Eq.sym (Bool.orFalse (Set.contains acc key))
    | [s, ..ss] =>
      rewrite Set.containsFoldUnion key ss (Set.union acc s), Set.containsUnion acc key s in
        Bool.orAssoc (Set.contains acc key) (Set.contains s key) (List.any ss (t => Set.contains t key))

--| `Set.unionAll` of a list of sets holds what some set in the list holds.
theorem Set.containsUnionAll [auto ord: Ord k] (sets: List (Set k)) (key: k):
    Set.contains (Set.unionAll sets) key = List.any sets (s => Set.contains s key) :=
  Set.containsFoldUnion key sets Set.empty

--| Folding a list of sets into `acc` by intersection holds what `acc` holds
--| and every set in the list does.
theorem Set.containsFoldIntersect [auto ord: Ord k] (key: k) (ss: List (Set k)) (acc: Set k):
    Set.contains (List.foldLeft ss acc Set.intersect) key = (Set.contains acc key ∧ List.all ss (s => Set.contains s key)) :=
  match ss with
    | [] => Eq.sym (Bool.andTrue (Set.contains acc key))
    | [s, ..ss] =>
      rewrite Set.containsFoldIntersect key ss (Set.intersect acc s), Set.containsIntersect acc key s in
        Bool.andAssoc (Set.contains acc key) (Set.contains s key) (List.all ss (t => Set.contains t key))

--| A set whose members are among the distinct keys of `universe`, and
--| agree with `yes` there, has as many members as `universe` has keys that
--| satisfy `yes`.
theorem Set.sizeOfMembers [auto ord: Ord k] (set: Set k) (universe: List k) (yes: k → Bool) (distinct: List.Distinct universe)
    (inside: ∀ (key: k) => Set.contains set key = True → List.contains universe key = True)
    (agree: ∀ (key: k) => List.contains universe key = True → Set.contains set key = yes key): Set.size set = List.length (List.filter universe yes) :=
  let same: List.Perm (Set.toList set) (List.filter universe yes) :=
    List.permOfSameMembers (Set.toList set) (List.filter universe yes) (Map.keysDistinct set.items) (List.distinctFilter universe yes distinct)
      (key member =>
        let found := (Set.memToList set key).forward member
        let known := inside key found
        List.memFilterIntro universe yes known.read (rewrite <- agree key known in found))
      (key member =>
        match List.memFilter universe yes member with
          | Both there held => (Set.memToList set key).backward (rewrite agree key ((List.memContains universe key).backward there) in held))
  Eq.trans (Set.sizeToList set) (List.permLength (Set.toList set) (List.filter universe yes) same)

--| An empty set holds no key.
theorem Set.missingOfIsEmpty [auto ord: Ord k] (s: Set k) (empty: Set.isEmpty s = True) (key: k): Set.contains s key = False :=
  match there: Set.contains s key with
    | False => rfl
    | True =>
      let zero: Set.size s = 0 := empty.read
      Void.exfalso (omega [Set.sizePositive s key there])

-- Maps of sets: what `get` finds after each operation, then `containsIn`

theorem Map.containsInEq [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v):
    m.containsIn key item = ((m.get key).getOrElse Set.empty).contains item := rfl

theorem Map.getInsertIn [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v):
    (m.insertIn key item).get key = Some (((m.get key).getOrElse Set.empty).insert item) :=
  Map.getAlter m key _

theorem Map.getInsertInOther [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v) (otherKey: k) (ne: otherKey ≠ key):
    (m.insertIn key item).get otherKey = m.get otherKey :=
  Map.getAlterOther m key otherKey ne _

theorem Map.getRemoveIn [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v):
    (m.removeIn key item).get key = ((m.get key).map (.remove item) |> .filter (rest => !rest.isEmpty)) :=
  Map.getAlter m key _

theorem Map.getRemoveInOther [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v) (otherKey: k) (ne: otherKey ≠ key):
    (m.removeIn key item).get otherKey = m.get otherKey :=
  Map.getAlterOther m key otherKey ne _

theorem Map.containsInEmpty [auto ord: Ord k] [auto itemOrd: Ord v] (key: k) (item: v):
    (Map.empty: Map k (Set v)).containsIn key item = False := rfl

--| The pair just inserted is there.
theorem Map.containsInInsertIn [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v):
    (m.insertIn key item).containsIn key item = True :=
  rewrite Map.containsInEq (m.insertIn key item) key item, Map.getInsertIn m key item in
    Set.containsInsert item ((m.get key).getOrElse Set.empty)

--| Inserting a pair leaves every other pair as it was.
theorem Map.containsInInsertInOther [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v) (otherKey: k) (otherItem: v)
    (ne: ¬(otherKey = key ∧ otherItem = item)): (m.insertIn key item).containsIn otherKey otherItem = m.containsIn otherKey otherItem :=
  match sameKey: otherKey == key with
    | False =>
      rewrite Map.containsInEq (m.insertIn key item) otherKey otherItem, Map.containsInEq m otherKey otherItem,
        Map.getInsertInOther m key item otherKey sameKey.read in rfl
    | True =>
      let isKey: otherKey = key := sameKey.read
      match sameItem: otherItem == item with
        | True => Void.exfalso (ne (Both isKey sameItem.read))
        | False =>
          rewrite isKey, Map.containsInEq (m.insertIn key item) key otherItem, Map.containsInEq m key otherItem, Map.getInsertIn m key item in
            Set.containsInsertOther ((m.get key).getOrElse Set.empty) item otherItem sameItem.read

--| The pair just removed is gone.
theorem Map.containsInRemoveIn [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v):
    (m.removeIn key item).containsIn key item = False :=
  rewrite Map.containsInEq (m.removeIn key item) key item, Map.getRemoveIn m key item in
    match found: m.get key with
      | None => rfl
      | Some s =>
        match gone: Set.isEmpty (Set.remove s item) with
          | True => rfl
          | False => Set.containsRemove s item

--| Removing a pair leaves every other pair as it was.
theorem Map.containsInRemoveInOther [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v) (otherKey: k) (otherItem: v)
    (ne: ¬(otherKey = key ∧ otherItem = item)): (m.removeIn key item).containsIn otherKey otherItem = m.containsIn otherKey otherItem :=
  match sameKey: otherKey == key with
    | False =>
      rewrite Map.containsInEq (m.removeIn key item) otherKey otherItem, Map.containsInEq m otherKey otherItem,
        Map.getRemoveInOther m key item otherKey sameKey.read in rfl
    | True =>
      let isKey: otherKey = key := sameKey.read
      match sameItem: otherItem == item with
        | True => Void.exfalso (ne (Both isKey sameItem.read))
        | False =>
          let differs: otherItem ≠ item := sameItem.read
          rewrite isKey, Map.containsInEq (m.removeIn key item) key otherItem, Map.containsInEq m key otherItem, Map.getRemoveIn m key item in
            match found: m.get key with
              | None => rfl
              | Some s =>
                match gone: Set.isEmpty (Set.remove s item) with
                  | True =>
                    rewrite <- Set.containsRemoveOther s item otherItem differs in
                      Eq.sym (Set.missingOfIsEmpty (Set.remove s item) gone otherItem)
                  | False => Set.containsRemoveOther s item otherItem differs

theorem Map.containsInInsertInIff [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v) (otherKey: k) (otherItem: v):
    ((m.insertIn key item).containsIn otherKey otherItem = True) ↔ ((otherKey = key ∧ otherItem = item) ∨ m.containsIn otherKey otherItem = True) := {
  forward = there =>
    match same: otherKey == key with
      | False => Inr (rewrite <- Map.containsInInsertInOther m key item otherKey otherItem (pair => same.read pair.left) in there)
      | True =>
        match sameItem: otherItem == item with
          | True => Inl (Both same.read sameItem.read)
          | False => Inr (rewrite <- Map.containsInInsertInOther m key item otherKey otherItem (pair => sameItem.read pair.right) in there),
  backward = found =>
    match found with
      | Inl pair => rewrite pair.left, pair.right in Map.containsInInsertIn m key item
      | Inr old =>
        match same: otherKey == key with
          | False => rewrite Map.containsInInsertInOther m key item otherKey otherItem (pair => same.read pair.left) in old
          | True =>
            match sameItem: otherItem == item with
              | True => rewrite same.read, sameItem.read in Map.containsInInsertIn m key item
              | False => rewrite Map.containsInInsertInOther m key item otherKey otherItem (pair => sameItem.read pair.right) in old
}

theorem Map.containsInRemoveInIff [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v) (otherKey: k) (otherItem: v):
    ((m.removeIn key item).containsIn otherKey otherItem = True) ↔ (¬(otherKey = key ∧ otherItem = item) ∧ m.containsIn otherKey otherItem = True) := {
  forward = there =>
    let differs: ¬(otherKey = key ∧ otherItem = item) := pair =>
      Bool.falseNotTrue (Eq.trans (Eq.sym (rewrite pair.left, pair.right in Map.containsInRemoveIn m key item)) there)
    Both differs (rewrite <- Map.containsInRemoveInOther m key item otherKey otherItem differs in there),
  backward = found => rewrite Map.containsInRemoveInOther m key item otherKey otherItem found.left in found.right
}

--| The entries `toList` walks hold exactly the pairs.
theorem Map.containsInToList [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v):
    (m.containsIn key item = True) ↔ (∃ (items: Set v) => ((key, items) ∈ m.toList) ∧ (items.contains item = True)) := {
  forward = there =>
    match found: m.get key with
      | Some s => Witness s (Both ((Map.memToList m key s).backward found) there),
  backward = found =>
    let (Witness s (Both member there)) := found
    rewrite Map.containsInEq m key item, (Map.memToList m key s).forward member in there
}
