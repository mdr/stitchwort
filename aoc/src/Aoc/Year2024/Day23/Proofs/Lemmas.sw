--| Facts about lists and sets that day 23's proofs use, not about the
--| puzzle.

namespace Aoc.Year2024.Day23.Proofs
import Std (Bool, DecEq, Eq, Iff, List, Map, Or, Set, Void)

theorem firstOfTwo ∀ (first second: a): List.Mem first [first, second] := Inl rfl

theorem secondOfTwo ∀ (first second: a): List.Mem second [first, second] := Inr (Inl rfl)

theorem sameKeyRefl ∀ [auto ord: Ord k] (key: k): Map.Spec.sameKey key key = True :=
  rewrite Map.Spec.sameKeyDecide key key in DecEq.refl key

--| What a set of three holds.
theorem threeElim ∀ [auto ord: Ord k] (first second third key: k) (goal: Prop)
    (held: (Set.fromList [first, second, third]).contains key = True)
    (isFirst: key = first → goal) (isSecond: key = second → goal) (isThird: key = third → goal):
    goal :=
  match (Set.containsFromListIff [first, second, third] key).forward held with
    | Inl same => isFirst (Eq.sym same)
    | Inr (Inl same) => isSecond (Eq.sym same)
    | Inr (Inr (Inl same)) => isThird (Eq.sym same)
    | Inr (Inr (Inr none)) => Void.exfalso none
