-- Facts about the search's queue, a `Set` of (cost, state) pairs, and its
-- settled `Map`, that std doesn't have.

namespace Aoc.Year2024.Day16.Proofs
import Aoc.Year2024.Day16 (..)
import Std (And, Bool, DecEq, Eq, Exists, List, Map, Nat, Option, Or, Ord, Ordering, Set, Void)

-- `Less` then anything is never a first comparison of `Greater`.
theorem notGreaterOfThen: (first: Ordering) → (second: Ordering) → Ordering.andThen first second = Less → Not (first = Greater)
  | Less, second, less, same => Ordering.lessNotGreater same
  | Equal, second, less, same => Ordering.equalNotGreater same
  | Greater, second, less, same => Ordering.greaterNotLess less

-- The least pair of a queue costs no more than any pair in it.
theorem minLeast [auto ord: Ord s] (queue: Set (Nat, s)) (cost: Nat) (state: s) (found: queue.min = Some (cost, state))
    (other: Nat) (otherState: s) (there: queue.contains (other, otherState) = True): cost ≤ other :=
  match entries: Map.toList queue.items with
    | Nil => Void.exfalso (Option.someNotNone (cost, state) (Eq.trans (Eq.sym found) (rewrite Map.minToList queue.items, entries in rfl)))
    | Cons (key, unit) rest =>
      let first: queue.min = Some key := rewrite Map.minToList queue.items, entries in rfl
      let same: key = (cost, state) := Option.someInjective _ _ (Eq.trans (Eq.sym first) found)
      let member := Map.memKeysOfContains queue.items (other, otherState) there
      rewrite entries at member in
        match member with
          | Inl here => rewrite Eq.cong Pair.fst (Eq.trans (Eq.sym same) here) in Nat.leRefl other
          | Inr later =>
            let sorted := Map.toListSorted queue.items
            rewrite entries at sorted in
              let (Both bottom ascending) := sorted
              let above := Map.Spec.keysAbove _ (other, otherState) (Some key) rest ascending later
              rewrite same at above in Nat.leOfCompare cost other (notGreaterOfThen _ _ above)

-- What's left after removing a key was there before.
theorem containsOfRemove [auto ord: Ord k] (set: Set k) (key: k) (other: k) (there: (set.remove key).contains other = True): set.contains other = True :=
  match same: other == key with
    | True =>
      let moved := Eq.cong (found => (set.remove key).contains found) (Eq.sym (DecEq.sound other key same))
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Set.containsRemove set key)) (Eq.trans moved there)))
    | False => Eq.trans (Eq.sym (Set.containsRemoveOther set key other (DecEq.soundFalse other key same))) there

-- Removing keeps every other key.
theorem containsRemoveKeeps [auto ord: Ord k] (set: Set k) (key: k) (other: k) (apart: Not (other = key)) (there: set.contains other = True):
    (set.remove key).contains other = True :=
  Eq.trans (Set.containsRemoveOther set key other apart) there

-- What pushing edges adds: each edge's state at `cost` plus its cost; the
-- queue keeps what it had.
theorem containsPushedKeeps [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (entry: (Nat, s)) →
    queue.contains entry = True → (pushEdges cost edges queue).contains entry = True
  | Nil, queue, entry, there => there
  | Cons (next, weight) rest, queue, entry, there =>
    containsPushedKeeps cost rest (queue.insert (cost + weight, next)) entry (Set.containsInsertMono queue (cost + weight, next) entry there)

theorem containsPushedEdge [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (next: s) → (weight: Nat) →
    (next, weight) ∈ edges → (pushEdges cost edges queue).contains (cost + weight, next) = True
  | Nil, queue, next, weight, member => Void.exfalso member
  | Cons (first, firstWeight) rest, queue, next, weight, Inl here =>
    rewrite <- Eq.cong Pair.fst here, <- Eq.cong Pair.snd here in
      containsPushedKeeps cost rest (queue.insert (cost + firstWeight, first)) (cost + firstWeight, first)
        (Set.containsInsert (cost + firstWeight, first) queue)
  | Cons (first, firstWeight) rest, queue, next, weight, Inr later =>
    containsPushedEdge cost rest (queue.insert (cost + firstWeight, first)) next weight later

-- Everything in the pushed queue was in the queue or is an edge's state.
theorem containsPushed [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (total: Nat) → (state: s) →
    (pushEdges cost edges queue).contains (total, state) = True →
    Or (queue.contains (total, state) = True) (Exists Nat (weight => And ((state, weight) ∈ edges) (total = cost + weight)))
  | Nil, queue, total, state, there => Inl there
  | Cons (next, weight) rest, queue, total, state, there =>
    match containsPushed cost rest (queue.insert (cost + weight, next)) total state there with
      | Inr (Witness found (Both member costs)) => Inr (Witness found (Both (Inr member) costs))
      | Inl inserted =>
        match same: (total, state) == (cost + weight, next) with
          | True =>
            let equal := DecEq.sound _ _ same
            Inr (Witness weight (Both (Inl (Eq.cong (found => (found, weight)) (Eq.sym (Eq.cong Pair.snd equal)))) (Eq.cong Pair.fst equal)))
          | False =>
            Inl (Eq.trans (Eq.sym (Set.containsInsertOther queue (cost + weight, next) (total, state) (DecEq.soundFalse _ _ same))) inserted)

-- What a map holds after an insert.
theorem getInsertCases [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (other: k) (found: v) (there: (m.insert key value).get other = Some found):
    Or (And (other = key) (found = value)) (m.get other = Some found) :=
  match same: other == key with
    | True =>
      let equal := DecEq.sound other key same
      Inl (Both equal (Option.someInjective _ _ (Eq.trans (Eq.sym there) (rewrite equal in Map.getInsert key value m))))
    | False => Inr (Eq.trans (Eq.sym (Map.getInsertOther key value other (DecEq.soundFalse other key same) m)) there)

-- Inserting a key not there keeps every entry.
theorem getInsertKeeps [auto ord: Ord k] (m: Map k v) (key: k) (value: v) (fresh: m.contains key = False) (other: k) (found: v)
    (there: m.get other = Some found): (m.insert key value).get other = Some found :=
  match same: other == key with
    | True =>
      let equal := DecEq.sound other key same
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym fresh) (rewrite <- equal in Map.containsOfGet m other found there)))
    | False => Eq.trans (Map.getInsertOther key value other (DecEq.soundFalse other key same) m) there

-- A key `contains` finds has a value.
theorem getOfContains [auto ord: Ord k] (m: Map k v) (key: k) (there: m.contains key = True): Exists v (value => m.get key = Some value) :=
  match found: m.get key with
    | Some value => Witness value rfl
    | None => Void.exfalso (Bool.falseNotTrue there)

-- A set with no least key holds nothing.
theorem missingOfMinNone [auto ord: Ord k] (set: Set k) (empty: set.min = None) (key: k): set.contains key = False :=
  match there: set.contains key with
    | False => rfl
    | True =>
      let member := Map.memKeysOfContains set.items key there
      match entries: Map.toList set.items with
        | Nil => Void.exfalso member
        | Cons entry rest =>
          let first: set.min = Some entry.fst := rewrite Map.minToList set.items, entries in rfl
          Void.exfalso (Option.someNotNone entry.fst (Eq.trans (Eq.sym first) empty))

-- `Ord.min` on numbers is at most either, and is one of them.
theorem ordMinBounds (x: Nat) (y: Nat): And (Ord.min x y ≤ x) (And (Ord.min x y ≤ y) (Or (Ord.min x y = x) (Ord.min x y = y))) :=
  match compared: Nat.compare x y with
    | Less => Both (Nat.leRefl x) (Both (Nat.leOfCompare x y (rewrite compared in Ordering.lessNotGreater)) (Inl rfl))
    | Equal => Both (Nat.leRefl x) (Both (Nat.leOfCompare x y (rewrite compared in Ordering.equalNotGreater)) (Inl rfl))
    | Greater =>
      let flipped: Nat.compare y x = Less := rewrite Nat.compareFlip x y, compared in rfl
      Both (Nat.lessLe y x (Nat.lessOfCompare y x flipped)) (Both (Nat.leRefl y) (Inr rfl))

-- Folding `Ord.min` gives at most the start and every member, and is one of
-- them.
theorem foldMinBounds: (xs: List Nat) → (start: Nat) →
    And (xs.foldLeft start Ord.min ≤ start)
      (And ((x: Nat) → x ∈ xs → xs.foldLeft start Ord.min ≤ x) (Or (xs.foldLeft start Ord.min = start) (xs.foldLeft start Ord.min ∈ xs)))
  | Nil, start => Both (Nat.leRefl start) (Both (x none => Void.exfalso none) (Inl rfl))
  | Cons first rest, start =>
    let (Both leStart (Both leFirst either)) := ordMinBounds start first
    let (Both below (Both belowAll isOne)) := foldMinBounds rest (Ord.min start first)
    Both (omega [below, leStart])
      (Both
        (x member =>
          match member with
            | Inl here => rewrite <- here in omega [below, leFirst]
            | Inr later => belowAll x later)
        (match isOne with
          | Inr inRest => Inr (Inr inRest)
          | Inl same =>
            match either with
              | Inl isStart => Inl (Eq.trans same isStart)
              | Inr isFirst => Inr (Inl (Eq.sym (Eq.trans same isFirst)))))

-- The least of a list is at most each member.
theorem minimumLeast: (xs: List Nat) → (least: Nat) → xs.minimum = Some least → (x: Nat) → x ∈ xs → least ≤ x
  | Nil, least, found, x, member => Void.exfalso member
  | Cons first rest, least, found, x, member =>
    let (Both leStart (Both leAll isOne)) := foldMinBounds rest first
    rewrite <- Option.someInjective _ _ found in
      match member with
        | Inl here => rewrite <- here in leStart
        | Inr later => leAll x later

-- The least of a list is on it.
theorem minimumMember: (xs: List Nat) → (least: Nat) → xs.minimum = Some least → least ∈ xs
  | Nil, least, found => Void.exfalso (Option.noneNotSome least found)
  | Cons first rest, least, found =>
    let (Both leStart (Both leAll isOne)) := foldMinBounds rest first
    rewrite <- Option.someInjective _ _ found in
      match isOne with
        | Inl isFirst => Inl (Eq.sym isFirst)
        | Inr inRest => Inr inRest

-- A list with a member has a least.
theorem minimumSome: (xs: List Nat) → (x: Nat) → x ∈ xs → Exists Nat (least => xs.minimum = Some least)
  | Nil, x, member => Void.exfalso member
  | Cons first rest, x, member => Witness (rest.foldLeft first Ord.min) rfl
