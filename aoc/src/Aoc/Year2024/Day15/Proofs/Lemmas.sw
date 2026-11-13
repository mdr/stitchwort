--| Facts the proofs need about cells: steps along a line never revisit a
--| cell. (The laws of single steps are `Aoc.Common.Proofs.offsetStep*`.)

namespace Aoc.Year2024.Day15.Proofs
import Aoc.Common (Direction)
import Aoc.Year2024.Day15 (..)
import Aoc.Year2024.Day15.Spec (ahead)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Int, List, Nat, Not, Or)

--| How far along `direction` a position is.
def progress (direction: Direction) (position: Cell): Int :=
  match direction with
    | Up => 0 - position.rows
    | Down => position.rows
    | Left => 0 - position.columns
    | Right => position.columns

theorem progressStep (position: Cell) (direction: Direction): progress direction (position.step direction) = progress direction position + 1 :=
  match direction with
    | Up => omega
    | Down => rfl
    | Left => omega
    | Right => rfl

theorem progressAhead (position: Cell) (direction: Direction) (count: Nat): progress direction (ahead position direction count) = progress direction position + count.toInt :=
  match count with
    | Zero => omega
    | Succ count => omega [progressStep (ahead position direction count) direction, progressAhead position direction count]

--| Steps along a line never come back.
theorem aheadInjective (position: Cell) (direction: Direction) (i: Nat) (j: Nat) (same: ahead position direction i = ahead position direction j): i = j :=
  omega [Eq.cong (progress direction) same, progressAhead position direction i, progressAhead position direction j]

--| Counting from the next position.
theorem aheadFrom (position: Cell) (direction: Direction) (count: Nat): ahead (position.step direction) direction count = ahead position direction (Succ count) :=
  match count with
    | Zero => rfl
    | Succ count => Eq.cong (here => here.step direction) (aheadFrom position direction count)

theorem aheadAddOne (position: Cell) (direction: Direction) (count: Nat):
    ahead position direction (count + 1) = (ahead position direction count).step direction :=
  rfl

--| Whether `position` is one of the `count` positions after `start`.
theorem decideAhead (start: Cell) (direction: Direction) (count: Nat) (position: Cell):
    (∃ (j: Nat) => j < count ∧ position = ahead start direction (j + 1)) ∨ (∀ (i: Nat) => i < count → position ≠ ahead start direction (i + 1)) :=
  match found: (List.range 0 count).any (i => position == ahead start direction (i + 1)) with
    | True =>
      let Witness j (Both member same) := found
      Inl (Witness j (Both (omega [List.memRangeFrom j count 0 member]) (DecEq.sound same)))
    | False =>
      Inr (i below same =>
        Bool.trueNotFalse
          (Eq.trans
            (Eq.sym
              (List.anyOfMem (List.range 0 count) _ i (rewrite same in DecEq.refl (ahead start direction (i + 1)))
                (List.memRangeFromIntro i count 0 (omega) (omega))))
            found))
