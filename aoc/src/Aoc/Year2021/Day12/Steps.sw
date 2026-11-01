-- What the search's termination needs: leaving out a cave that was in the
-- list of unvisited ones makes the list shorter.

namespace Aoc.Year2021.Day12
import Std (Bool, DecEq, List, Nat, Void)

-- Filtering keeps at most what there was.
theorem filterNoLonger (keep: a → Bool): (xs: List a) → (xs.filter keep).length ≤ xs.length
  | Nil => rfl
  | Cons x rest =>
    match keep x with
      | True => filterNoLonger keep rest
      | False => omega [filterNoLonger keep rest]

-- Filtering out an element that is there makes the list shorter.
theorem filterDropsShorter (keep: a → Bool) (x: a) (dropped: keep x = False): (xs: List a) → x ∈ xs → (xs.filter keep).length < xs.length
  | Nil, member => Void.exfalso member
  | Cons y rest, member =>
    match member with
      | Inl same => rewrite same, dropped in omega [filterNoLonger keep rest]
      | Inr later =>
        match keep y with
          | True => filterDropsShorter keep x dropped rest later
          | False => omega [filterDropsShorter keep x dropped rest later]

-- Leaving out a cave that is there makes the list shorter.
theorem withoutShorter (caves: List Text) (cave: Text) (member: cave ∈ caves): (without caves cave).length < caves.length :=
  filterDropsShorter (c => not (c == cave)) cave (rewrite DecEq.refl cave in rfl) caves member
