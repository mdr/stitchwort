-- Facts the proofs need: steps along a line never revisit a position, what
-- the set operations the moves use do to membership, and that a set holding
-- `count` different positions has at least `count` elements.

namespace Aoc.Year2024.Day15.Proofs
import Aoc.Year2024.Day15 (..)
import Aoc.Year2024.Day15.Spec (ahead)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Int, List, Map, Nat, Not, Or, Set, Void)

-- How far along `direction` a position is.
def progress (direction: Direction) (position: Position): Int :=
  match direction with
    | Up => 0 - position.row
    | Down => position.row
    | Left => 0 - position.column
    | Right => position.column

theorem progressStep (position: Position): (direction: Direction) → progress direction (position.step direction) = progress direction position + 1
  | Up => omega
  | Down => rfl
  | Left => omega
  | Right => rfl

theorem progressAhead (position: Position) (direction: Direction): (count: Nat) → progress direction (ahead position direction count) = progress direction position + count.toInt
  | Zero => omega
  | Succ count => omega [progressStep (ahead position direction count) direction, progressAhead position direction count]

-- Steps along a line never come back.
theorem aheadInjective (position: Position) (direction: Direction) (i: Nat) (j: Nat) (same: ahead position direction i = ahead position direction j): i = j :=
  omega [Eq.cong (progress direction) same, progressAhead position direction i, progressAhead position direction j]

-- Counting from the next position.
theorem aheadFrom (position: Position) (direction: Direction): (count: Nat) → ahead (position.step direction) direction count = ahead position direction (Succ count)
  | Zero => rfl
  | Succ count => Eq.cong (here => here.step direction) (aheadFrom position direction count)

theorem aheadAddOne (position: Position) (direction: Direction) (count: Nat):
    ahead position direction (count + 1) = (ahead position direction count).step direction :=
  rewrite Nat.addOne count in rfl

-- Whether `position` is one of the `count` positions after `start`.
theorem decideAhead (start: Position) (direction: Direction) (count: Nat) (position: Position):
    Or (∃ (j: Nat) => j < count ∧ position = ahead start direction (j + 1))
      ((i: Nat) → i < count → Not (position = ahead start direction (i + 1))) :=
  match found: (List.range count).any (i => position == ahead start direction (i + 1)) with
    | True =>
      List.anyTrueElim (List.range count) _ _ found
        (j member same => Inl (Witness j (Both (omega [List.memRangeFrom j count 0 member]) (DecEq.sound _ _ same))))
    | False =>
      Inr (i below same =>
        Bool.trueNotFalse
          (Eq.trans
            (Eq.sym
              (List.anyOfMem (List.range count) _ i (rewrite same in DecEq.refl (ahead start direction (i + 1)))
                (List.memRangeFromIntro i count 0 (omega) (omega))))
            found))

-- Sets.

-- A set holding something isn't empty.
theorem sizePositive (set: Set Position) (key: Position) (member: set.contains key = True): 1 ≤ set.size :=
  match c: set.toList with
    | Nil => Void.exfalso (rewrite c at (Map.memKeysOfContains set.items key member: List.Mem key (Set.toList set)))
    | Cons first rest => rewrite Set.sizeToList set, c in omega

-- A set holding `count` different positions, `at 0` to `at (count - 1)`,
-- has at least `count` elements.
theorem countAtMostSize (at: Nat → Position): (count: Nat) → (set: Set Position) →
    ((i: Nat) → i < count → set.contains (at i) = True) → ((i: Nat) → (j: Nat) → i < count → j < count → at i = at j → i = j) → count ≤ set.size
  | Zero, set, members, different => omega
  | Succ count, set, members, different =>
    let rest := set.remove (at count)
    let restMembers: (i: Nat) → i < count → rest.contains (at i) = True := i below =>
      rewrite Set.containsRemoveOther set (at count) (at i) (same => omega [different i count (omega) (omega) same]) in members i (omega)
    let smaller := countAtMostSize at count rest restMembers (i j below belowJ same => different i j (omega) (omega) same)
    let removed: rest.size = set.size - 1 := rewrite Map.sizeRemove set.items (at count), members count (omega) in rfl
    omega [sizePositive set (at count) (members count (omega))]
