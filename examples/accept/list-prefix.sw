-- `List.startsWith`, `List.stripPrefix` and `List.isEmpty`, as `Text` has
-- them, with the prefix lemmas.

import Std (Bool, DecEq, Eq, List, Nat, Option)

def afterHeader (lines: List Nat): Option (List Nat) := lines.stripPrefix [0, 0]

theorem afterHeaderSome (rest: List Nat): afterHeader (List.append [0, 0] rest) = Some rest :=
  List.stripPrefixAppend [0, 0] rest

theorem afterHeaderStarts (lines: List Nat):
    afterHeader lines = (if lines.startsWith [0, 0] then Some (lines.drop 2) else None) :=
  List.stripPrefixStartsWith lines [0, 0]

theorem prefixShorter (xs: List Nat) (starts: xs.startsWith [1, 2, 3] = True): 3 ≤ xs.length :=
  List.startsWithLength xs [1, 2, 3] starts

theorem emptyIsNil (xs: List Nat): xs.isEmpty = (xs == []) := List.isEmptyEqNil xs

theorem examples: And ([1, 2, 3].startsWith [1, 2] = True) ([1, 2].stripPrefix [1, 3] = None) := Both rfl rfl
