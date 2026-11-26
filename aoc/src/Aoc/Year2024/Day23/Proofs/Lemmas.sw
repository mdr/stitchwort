--| Facts about lists and sets that day 23's proofs use, not about the
--| puzzle.

namespace Aoc.Year2024.Day23.Proofs
import Std (Bool, DecEq, Eq, Iff, List, Map, Or, Set, Void)

theorem sameKeyRefl ∀ [auto ord: Ord k] (key: k): Map.Spec.sameKey key key = True :=
  rewrite Map.Spec.sameKeyDecide key key then DecEq.refl key

--| What a set of three holds.
theorem threeElim ∀ [auto ord: Ord k] (first second third key: k) (goal: Prop)
    (held: (Set.fromList [first, second, third]).contains key = True)
    (isFirst: key = first → goal) (isSecond: key = second → goal) (isThird: key = third → goal):
    goal :=
  match (Set.containsFromListIff [first, second, third] key).forward held with
    | Inl same => isFirst same.flipped
    | Inr (Inl same) => isSecond same.flipped
    | Inr (Inr (Inl same)) => isThird same.flipped
    | Inr (Inr (Inr none)) => none.impossible
