-- Derived `Ord` for an enumeration (docs/proposals/interfaces.md §5.11):
-- constructors compare in the order they're declared. Nothing is written
-- for it: `List.sort`, `Ord.max` and the laws work at once.

import Std (List, Ord, Ordering)

type Suit = | Clubs | Diamonds | Hearts | Spades

test "declared order" := Ord.compare Clubs Spades == Less
test "the other way" := Ord.compare Spades Hearts == Greater
test "equal" := Ord.compare Hearts Hearts == Equal
test "sort" := List.sort [Spades, Clubs, Hearts, Diamonds, Clubs] == [Clubs, Clubs, Diamonds, Hearts, Spades]
test "max" := Ord.max Diamonds Hearts == Hearts
test "maximum" := List.maximum [Diamonds, Spades, Clubs] == Some Spades

-- The laws are the instance's, for any suits.
theorem suitSelf (s: Suit): Ord.compare s s = Equal := Ord.compareSelf s

theorem suitFlip (s: Suit) (t: Suit): Ord.compare t s = Ordering.flip (Ord.compare s t) := Ord.flip s t
