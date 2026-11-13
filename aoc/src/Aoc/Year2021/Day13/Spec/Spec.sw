--| Day 13 as the puzzle states it, over the program's types for a dot (`x`
--| across, `y` down) and a fold (`AlongX line`, `AlongY line`). The sheet's
--| dots are a set, written as the proposition "this spot has a dot". The
--| proofs (Proofs/) show the program's answers are these.

namespace Aoc.Year2021.Day13.Spec
import Aoc.Common (Point)
import Aoc.Year2021.Day13 (Fold)
import Std (List)

--| Where a dot lands when the sheet is folded: a dot on the near side of the
--| line (the top or the left) stays where it is; one on the far side lands
--| at its mirror image, as far from the line on the near side (so the line
--| is halfway between the two). A dot on the line, or further beyond it than
--| the sheet reaches on the near side, lands nowhere: the puzzle promises
--| there are none (`Promise`).
def Lands (fold: Fold) (dot: Point) (spot: Point): Prop := match fold with
  | AlongY line => spot.x = dot.x ∧ ((dot.y < line ∧ spot.y = dot.y) ∨ (line < dot.y ∧ spot.y + dot.y = 2 * line))
  | AlongX line => spot.y = dot.y ∧ ((dot.x < line ∧ spot.x = dot.x) ∨ (line < dot.x ∧ spot.x + dot.x = 2 * line))

--| After a fold, a spot has a dot when some dot lands there: the dots after
--| the fold are the image of the dots before it.
def AfterFold (fold: Fold) (marked: Point → Prop) (spot: Point): Prop := ∃ (dot: Point) => marked dot ∧ Lands fold dot spot

--| The dots after the folds, one after another.
def AfterFolds: List Fold → (Point → Prop) → Point → Prop
  | [], marked, spot => marked spot
  | [fold, ..rest], marked, spot => AfterFolds rest (AfterFold fold marked) spot

--| The sheet's dots at the start: those the input lists (a dot listed twice
--| is one dot).
def Listed (dots: List Point) (spot: Point): Prop := spot ∈ dots

--| What the puzzle promises: when a fold is made, no dot is on its line, and
--| none is further beyond it than the line is from the near edge (the
--| puzzle's folds are at the middle of the sheet; a dot further out would
--| land off the sheet).
def Clear (fold: Fold) (dot: Point): Prop := match fold with
  | AlongY line => dot.y ≠ line ∧ dot.y ≤ 2 * line
  | AlongX line => dot.x ≠ line ∧ dot.x ≤ 2 * line

def Promise: List Fold → (Point → Prop) → Prop
  | [], marked => Unit
  | [fold, ..rest], marked => (∀ (dot: Point) => marked dot → Clear fold dot) ∧ Promise rest (AfterFold fold marked)

--| Part 1's answer is how many dots there are: `count` of them, listed
--| without repeats, exactly the dots.
def DotCount (marked: Point → Prop) (count: Nat): Prop :=
  ∃ (dots: List Point) => List.Distinct dots ∧ (∀ (spot: Point) => spot ∈ dots ↔ marked spot) ∧ dots.length = count

--| Part 2's answer is a picture: rows of `#` and `.`, the top row first, all
--| the same width, the top left character at `x = 0, y = 0`. The character
--| at a spot is the picture's cell at the spot's position (row `y`,
--| column `x`).
def cellAt (picture: List (List Char)) (spot: Point): Option Char := Aoc.Common.cellAt picture spot.toPosition

--| The picture shows the dots when every dot is a `#` in it, every `#` is a
--| dot, and every other character is a `.`; its rows are all the same width.
def Shows (picture: List (List Char)) (marked: Point → Prop): Prop :=
  (∀ (spot: Point) => marked spot → cellAt picture spot = Some '#')
    ∧ (∀ (spot: Point) => cellAt picture spot = Some '#' → marked spot)
    ∧ (∀ (spot: Point) (c: Char) => cellAt picture spot = Some c → c = '#' ∨ c = '.')
    ∧ (∀ (row: List Char) => row ∈ picture → ∀ (other: List Char) => other ∈ picture → row.length = other.length)
