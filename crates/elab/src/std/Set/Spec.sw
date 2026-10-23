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
