-- Facts about lists and sets that day 23's proofs use, not about the
-- puzzle.

namespace Aoc.Year2024.Day23.Proofs
import Std (Bool, DecEq, Eq, Iff, List, Map, Or, Set, Void)

theorem firstOfTwo (first: a) (second: a): List.Mem first [first, second] := Inl rfl

theorem secondOfTwo (first: a) (second: a): List.Mem second [first, second] := Inr (Inl rfl)
