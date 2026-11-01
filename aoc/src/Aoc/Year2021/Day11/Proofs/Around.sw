-- The program's eight positions around an octopus are the spec's adjacent
-- ones, and counting the flashers among them counts the spec's flashing
-- neighbours.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Std (Bool, DecEq, Eq, Exists, Iff, List, Nat, Option, Void)

theorem adjacentOfBounds (r: Nat) (c: Nat) (a: Nat) (b: Nat) (h1: r - 1 ≤ a) (h2: a ≤ r + 1) (h3: c - 1 ≤ b) (h4: b ≤ c + 1)
    (other: not (a == r && b == c) = True): adjacent (r, c) (a, b) = True :=
  cases

theorem rowAboveOfAdjacent (r: Nat) (c: Nat) (a: Nat) (b: Nat) (near: adjacent (r, c) (a, b) = True): r - 1 ≤ a := cases
theorem rowBelowOfAdjacent (r: Nat) (c: Nat) (a: Nat) (b: Nat) (near: adjacent (r, c) (a, b) = True): a ≤ r + 1 := cases
theorem columnLeftOfAdjacent (r: Nat) (c: Nat) (a: Nat) (b: Nat) (near: adjacent (r, c) (a, b) = True): c - 1 ≤ b := cases
theorem columnRightOfAdjacent (r: Nat) (c: Nat) (a: Nat) (b: Nat) (near: adjacent (r, c) (a, b) = True): b ≤ c + 1 := cases
theorem otherOfAdjacent (r: Nat) (c: Nat) (a: Nat) (b: Nat) (near: adjacent (r, c) (a, b) = True): not (a == r && b == c) = True := cases

-- The rows and columns `around` takes the positions from.
def aroundBlock (r: Nat) (c: Nat): List (Nat, Nat) :=
  List.between (r - 1) (r + 1) |> .flatMap (row => List.between (c - 1) (c + 1) |> .map (column => (row, column)))

-- Around (r, c) are exactly the positions adjacent to it.
theorem adjacentOfAround (r: Nat) (c: Nat) (a: Nat) (b: Nat) (member: (a, b) ∈ around (r, c)): adjacent (r, c) (a, b) = True :=
  let (Both inBlock other) := List.memFilter (aroundBlock r c) (near => not (near.fst == r && near.snd == c)) (a, b) member
  List.anyElim (row => (a, b) ∈ List.map (List.between (c - 1) (c + 1)) (column => (row, column))) (adjacent (r, c) (a, b) = True)
    (List.between (r - 1) (r + 1))
    (List.memFlatMapElim (row => List.map (List.between (c - 1) (c + 1)) (column => (row, column))) (a, b) (List.between (r - 1) (r + 1)) inBlock)
    (row inRows inRow =>
      Exists.elim (List.memMapElim (column => (row, column)) (a, b) (List.between (c - 1) (c + 1)) inRow) (column both =>
        let (Both inColumns same) := both
        let sameRow: row = a := Eq.cong Pair.fst same
        let sameColumn: column = b := Eq.cong Pair.snd same
        let (Both rowAbove rowBelow) := List.memBetween inRows
        let (Both columnLeft columnRight) := List.memBetween inColumns
        adjacentOfBounds r c a b (omega) (omega) (omega) (omega) other))

theorem aroundOfAdjacent (r: Nat) (c: Nat) (a: Nat) (b: Nat) (near: adjacent (r, c) (a, b) = True): (a, b) ∈ around (r, c) :=
  List.memFilterIntro (aroundBlock r c) (near => not (near.fst == r && near.snd == c)) (a, b)
    (List.memFlatMapIntro (row => List.map (List.between (c - 1) (c + 1)) (column => (row, column))) a (a, b) (List.between (r - 1) (r + 1))
      (List.memBetweenIntro a (r - 1) (r + 1) (rowAboveOfAdjacent r c a b near) (rowBelowOfAdjacent r c a b near))
      (List.memMap (List.between (c - 1) (c + 1)) b
        (List.memBetweenIntro b (c - 1) (c + 1) (columnLeftOfAdjacent r c a b near) (columnRightOfAdjacent r c a b near)) (column => (a, column))))
    (otherOfAdjacent r c a b near)

-- Counting the flashers around (r, c) counts the spec's flashing
-- neighbours, when only octopuses on the grid flash.
theorem countAround (levels: List (List Nat)) (flashed: (Nat, Nat) → Bool)
    (onGrid: (q: (Nat, Nat)) → flashed q = True → q ∈ levels.gridCells.map Pair.fst) (r: Nat) (c: Nat):
    (around (r, c)).count flashed = flashingNeighbours levels flashed (r, c) :=
  let positions := levels.gridCells.map Pair.fst
  let near := (q: (Nat, Nat)) => adjacent (r, c) q && flashed q
  let same: List.Perm ((around (r, c)).filter flashed) (positions.filter near) :=
    List.permOfSameMembers ((around (r, c)).filter flashed) (positions.filter near)
      (List.distinctFilter (around (r, c)) flashed (aroundDistinct r c))
      (List.distinctFilter positions near (positionsDistinct levels))
      (q member =>
        let (Both inAround flashes) := List.memFilter (around (r, c)) flashed q member
        List.memFilterIntro positions near q (onGrid q flashes) (Bool.andIntro _ _ (adjacentOfAroundAt r c q inAround) flashes))
      (q member =>
        let (Both inGrid both) := List.memFilter positions near q member
        List.memFilterIntro (around (r, c)) flashed q (aroundOfAdjacentAt r c q (Bool.andLeft _ _ both)) (Bool.andRight _ _ both))
  calc (around (r, c)).count flashed
    _ = ((around (r, c)).filter flashed).length := Eq.sym (List.lengthFilter (around (r, c)) flashed)
    _ = (positions.filter near).length := List.permLength _ _ same
    _ = positions.count near := List.lengthFilter positions near
    _ = flashingNeighbours levels flashed (r, c) := List.countMap levels.gridCells near Pair.fst

theorem adjacentOfAroundAt (r: Nat) (c: Nat): (q: (Nat, Nat)) → q ∈ around (r, c) → adjacent (r, c) q = True
  | (a, b), member => adjacentOfAround r c a b member

theorem aroundOfAdjacentAt (r: Nat) (c: Nat): (q: (Nat, Nat)) → adjacent (r, c) q = True → q ∈ around (r, c)
  | (a, b), near => aroundOfAdjacent r c a b near

-- No position is around (r, c) twice.
theorem aroundDistinct (r: Nat) (c: Nat): List.Distinct (around (r, c)) :=
  List.distinctFilter (aroundBlock r c) (near => not (near.fst == r && near.snd == c))
    (List.distinctFlatMap (row => List.map (List.between (c - 1) (c + 1)) (column => (row, column))) Pair.fst (List.between (r - 1) (r + 1))
      (List.distinctBetween (r - 1) (r + 1))
      (row inRows =>
        List.distinctMap (List.between (c - 1) (c + 1)) (List.distinctBetween (c - 1) (c + 1)) (column => (row, column))
          (x y same => Eq.cong Pair.snd same))
      (row inRows position inRow =>
        Exists.elim (List.memMapElim (column => (row, column)) position (List.between (c - 1) (c + 1)) inRow) (column both =>
          rewrite <- And.right both in rfl)))
