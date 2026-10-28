-- `noOverlap` decides the spec's `List.Distinct`: it is `True` exactly when
-- no two positions are the same (`noOverlapCorrect`).

namespace Aoc.Year2024.Day14.Proofs
import Aoc.Year2024.Day14 (..)
import Std (And, Bool, DecEq, Eq, Iff, List, Set, Void)

-- What has been seen is not ahead in the list.
theorem seenNotAhead (seen: Set Position) (position: Position) (isSeen: seen.contains position = True):
    (positions: List Position) → noOverlapFrom seen positions = True → position ∉ positions
  | Nil, ok, member => member
  | Cons next rest, ok, member =>
    match c: seen.contains next with
      | True => Bool.falseNotTrue ok
      | False =>
        match member with
          | Inl same => Bool.falseNotTrue (Eq.trans (Eq.sym c) (rewrite same in isSeen))
          | Inr later => seenNotAhead (seen.insert next) position (Set.containsInsertMono seen next position isSeen) rest ok later

-- Passing the loop means no repeats.
theorem passDistinct: (seen: Set Position) → (positions: List Position) → noOverlapFrom seen positions = True → List.Distinct positions
  | seen, Nil, ok => Trivial
  | seen, Cons next rest, ok =>
    match c: seen.contains next with
      | True => Void.exfalso (Bool.falseNotTrue ok)
      | False =>
        Both (seenNotAhead (seen.insert next) next (Set.containsInsert next seen) rest ok) (passDistinct (seen.insert next) rest ok)

-- No repeats, and nothing seen already, passes the loop.
theorem distinctPass: (seen: Set Position) → (positions: List Position) → List.Distinct positions →
    ((position: Position) → position ∈ positions → seen.contains position = False) → noOverlapFrom seen positions = True
  | seen, Nil, distinct, unseen => rfl
  | seen, Cons next rest, distinct, unseen =>
    rewrite unseen next (Inl rfl)
    in distinctPass (seen.insert next) rest (And.right distinct) (position member =>
      rewrite Set.containsInsertOther seen next position (same => And.left distinct (rewrite <- same in member))
      in unseen position (Inr member))

theorem noOverlapCorrect (positions: List Position): noOverlap positions = True ↔ List.Distinct positions := {
  forward = ok => passDistinct Set.empty positions ok,
  backward = distinct => distinctPass Set.empty positions distinct (position member => rfl)
}
