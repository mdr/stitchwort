-- Facts about lists and sets that day 23's proofs use, not about the
-- puzzle.

namespace Aoc.Year2024.Day23.Proofs
import Std (Bool, DecEq, Eq, Iff, List, Map, Or, Set, Void)

theorem firstOfTwo (first: a) (second: a): List.Mem first [first, second] := Inl rfl

theorem secondOfTwo (first: a) (second: a): List.Mem second [first, second] := Inr (Inl rfl)

theorem sameKeyRefl [auto ord: Ord k] (key: k): Map.Spec.sameKey key key = True :=
  rewrite Map.Spec.sameKeyDecide key key in DecEq.refl key

-- A set made from a list holds its elements.
theorem containsFromListOfMem [auto ord: Ord k] (key: k) (keys: List k) (listed: List.Mem key keys): (Set.fromList keys).contains key = True :=
  rewrite Set.containsFromList key keys in List.anyOfMem keys (x => Map.Spec.sameKey key x) key (sameKeyRefl key) listed

-- ...and nothing else.
theorem memOfContainsFromList [auto ord: Ord k] (key: k) (keys: List k) (held: (Set.fromList keys).contains key = True): List.Mem key keys :=
  List.anyTrueElim keys (x => Map.Spec.sameKey key x) (List.Mem key keys) (rewrite <- Set.containsFromList key keys in held)
    (x listed same => rewrite Map.Spec.sameKeySound key x same in listed)

-- What a set of three holds.
theorem threeElim [auto ord: Ord k] (first: k) (second: k) (third: k) (key: k) (goal: Prop)
    (held: (Set.fromList [first, second, third]).contains key = True) (isFirst: key = first → goal) (isSecond: key = second → goal)
    (isThird: key = third → goal): goal :=
  match memOfContainsFromList key [first, second, third] held with
    | Inl same => isFirst (Eq.sym same)
    | Inr (Inl same) => isSecond (Eq.sym same)
    | Inr (Inr (Inl same)) => isThird (Eq.sym same)
    | Inr (Inr (Inr none)) => Void.exfalso none
