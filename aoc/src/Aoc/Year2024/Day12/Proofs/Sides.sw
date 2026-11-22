--| Part 2: the program counts a region's corners, the spec its sides, and
--| the two agree for every region (`sidesCorrect`), through the grid of
--| booleans of Corners.sw: the program's corners at a plot are the grid's
--| (`programCornersCell`), the spec's first sections of fence the grid's
--| starts (`specSidesCell`), and a sum over the region's plots is a sum over
--| a square of the grid big enough to hold it (`sumOverGrid`).

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Common (Direction, Position, directions)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Nat, Option, Or, Void)

--| The region as a grid of booleans.
def insideOf (region: Region) (row column: Nat): Bool := region.contains { row, column }

theorem countDirections ∀ (f: Direction → Bool):
    directions.count f = Bool.toNat (f Up) + Bool.toNat (f Down) + Bool.toNat (f Left) + Bool.toNat (f Right) :=
  rewrite List.countCons [Right, Down, Left] Up f,
      List.countCons [Down, Left] Right f,
      List.countCons [Left] Down f,
      List.countCons [] Left f then
    arithmetic

theorem countQuadrants ∀ (f: (Direction, Direction) → Bool):
    quadrants.count f
      = Bool.toNat (f (Up, Left))
        + Bool.toNat (f (Up, Right))
        + Bool.toNat (f (Down, Left))
        + Bool.toNat (f (Down, Right)) :=
  rewrite List.countCons [(Up, Right), (Down, Left), (Down, Right)] (Up, Left) f,
      List.countCons [(Down, Left), (Down, Right)] (Up, Right) f,
      List.countCons [(Down, Right)] (Down, Left) f,
      List.countCons [] (Down, Right) f then
    arithmetic

--| The spec's first sections of fence at a plot are the grid's starts.
theorem specSidesCell ∀ (region: Region) (row column: Nat):
    directions.count (isFirstSection region { row, column }) = starts (insideOf region) row column :=
  match row, column with
    | Zero | Succ _, Zero | Succ _ => Eq.trans (countDirections (isFirstSection region _)) byComputing

--| Each side of a plot touches the region where the grid's neighbour is in.
theorem facesUp ∀ (region: Region) (row column: Nat):
    facesRegion region { row, column } Up = above (insideOf region) row column :=
  match row with | Zero | Succ _ => byComputing

theorem facesDown ∀ (region: Region) (row column: Nat):
    facesRegion region { row, column } Down = below (insideOf region) row column :=
  byComputing

theorem facesLeft ∀ (region: Region) (row column: Nat):
    facesRegion region { row, column } Left = leftOf (insideOf region) row column :=
  match column with | Zero | Succ _ => byComputing

theorem facesRight ∀ (region: Region) (row column: Nat):
    facesRegion region { row, column } Right = rightOf (insideOf region) row column :=
  byComputing

--| Whether the plot diagonally across a corner, one step `vertical` then one
--| `horizontal`, is in the region.
def diagonalIn (region: Region) (plot: Position) (vertical horizontal: Direction): Bool := match plot.step vertical with
  | Some next => facesRegion region next horizontal
  | None => False

theorem diagonalUpLeft ∀ (region: Region) (row column: Nat):
    diagonalIn region { row, column } Up Left = above (leftOf (insideOf region)) row column :=
  match row, column with
    | Zero, column => byComputing
    | Succ _, Zero | Succ _ => byComputing

theorem diagonalUpRight ∀ (region: Region) (row column: Nat):
    diagonalIn region { row, column } Up Right = above (rightOf (insideOf region)) row column :=
  match row with | Zero | Succ _ => byComputing

theorem diagonalDownLeft ∀ (region: Region) (row column: Nat):
    diagonalIn region { row, column } Down Left = below (leftOf (insideOf region)) row column :=
  match column with | Zero | Succ _ => byComputing

theorem diagonalDownRight ∀ (region: Region) (row column: Nat):
    diagonalIn region { row, column } Down Right = below (rightOf (insideOf region)) row column :=
  byComputing

--| `!=` is `!` of `==`.
theorem notEqualNot ∀ (x y: Option Char): ((x != y): Bool) = Bool.not (x == y) := byComputing

--| Where a side of a plot in a region faces the same plant, the plot
--| diagonally across grows another exactly when it isn't in the region.
theorem diagonalSame ∀ (garden: Garden) (start: Position) (plant: Char)
    (grows: garden.plantAt start = Some plant) (region: Region)
    (isRegion: IsRegion garden start region) (plot: Position)
    (member: plot ∈ region.plots) (vertical horizontal: Direction)
    (same: garden.sameAcross plot vertical = True):
    (((plot.diagonal vertical horizontal |> .flatMap garden.plantAt) != garden.plantAt plot): Bool)
      = Bool.not (diagonalIn region plot vertical horizontal) :=
  let plotGrows := joinedPlant garden plant start plot grows ((isRegion plot).forward member)
  let faces :=
    Eq.trans (Eq.flipped (sameAcrossFaces garden start plant grows region isRegion plot member vertical)) same
  match stepped: plot.step vertical with
    | Some next =>
      let nextIn := faces.read
      let nextGrows := joinedPlant garden plant start next grows ((isRegion next).forward nextIn)
      rewrite notEqualNot,
          plotGrows,
          <- sameAcrossFaces garden start plant grows region isRegion next nextIn horizontal,
          nextGrows

--| A corner of the program's, split into outside and inside.
theorem isCornerSplit ∀ (garden: Garden) (plot: Position)
    (vertical horizontal: Direction) (verticalIn horizontalIn diagonal: Bool)
    (verticalSame: garden.sameAcross plot vertical = verticalIn)
    (horizontalSame: garden.sameAcross plot horizontal = horizontalIn)
    (across: verticalIn = True
      → (((plot.diagonal vertical horizontal |> .flatMap garden.plantAt) != garden.plantAt plot): Bool)
        = Bool.not diagonal):
    Bool.toNat (garden.isCorner plot vertical horizontal)
      = Bool.toNat (convex True verticalIn horizontalIn) + Bool.toNat (concave True verticalIn horizontalIn diagonal) :=
  rewrite verticalSame, horizontalSame then
    match verticalIn, horizontalIn with
      | False, False | True => byComputing
      | True, False => byComputing
      | True, True =>
        rewrite across byComputing then
          match diagonal with
            | True | False => byComputing

--| The program's corners at a plot of a region are the grid's.
theorem programCornersCell ∀ (garden: Garden) (start: Position) (plant: Char)
    (grows: garden.plantAt start = Some plant) (region: Region)
    (isRegion: IsRegion garden start region) (plot: Position)
    (member: plot ∈ region.plots):
    garden.cornerCount plot = corners (insideOf region) plot.row plot.column :=
  match plot with
    | { row, column } =>
      let plot: Position := { row, column }
      let inside := insideOf region
      let isIn: inside row column = True := member
      let faces := (side: Direction) => sameAcrossFaces garden start plant grows region isRegion plot member side
      let up := Eq.trans (faces Up) (facesUp region row column)
      let down := Eq.trans (faces Down) (facesDown region row column)
      let left := Eq.trans (faces Left) (facesLeft region row column)
      let right := Eq.trans (faces Right) (facesRight region row column)
      let diagonal := (vertical: Direction) =>
        (horizontal: Direction) =>
          (same: garden.sameAcross plot vertical = True) =>
            diagonalSame garden start plant grows region isRegion plot member vertical horizontal same
      arithmetic [
        countQuadrants (quadrant => garden.isCorner plot quadrant.fst quadrant.snd),
        isCornerSplit garden plot Up Left
          (above inside row column)
          (leftOf inside row column)
          (above (leftOf inside) row column)
          up
          left
          (same => rewrite <- diagonalUpLeft region row column then diagonal Up Left (Eq.trans up same)),
        isCornerSplit garden plot Up Right
          (above inside row column)
          (rightOf inside row column)
          (above (rightOf inside) row column)
          up
          right
          (same => rewrite <- diagonalUpRight region row column then diagonal Up Right (Eq.trans up same)),
        isCornerSplit garden plot Down Left
          (below inside row column)
          (leftOf inside row column)
          (below (leftOf inside) row column)
          down
          left
          (same => rewrite <- diagonalDownLeft region row column then diagonal Down Left (Eq.trans down same)),
        isCornerSplit garden plot Down Right
          (below inside row column)
          (rightOf inside row column)
          (below (rightOf inside) row column)
          down
          right
          (same => rewrite <- diagonalDownRight region row column then diagonal Down Right (Eq.trans down same)),
        (rewrite isIn: corners inside row column
          = Bool.toNat (convex True (above inside row column) (leftOf inside row column))
            + Bool.toNat
              (concave True (above inside row column) (leftOf inside row column) (above (leftOf inside) row column))
            + (Bool.toNat (convex True (above inside row column) (rightOf inside row column))
              + Bool.toNat
                (concave True
                  (above inside row column)
                  (rightOf inside row column)
                  (above (rightOf inside) row column)))
            + (Bool.toNat (convex True (below inside row column) (leftOf inside row column))
              + Bool.toNat
                (concave True (below inside row column) (leftOf inside row column) (below (leftOf inside) row column)))
            + (Bool.toNat (convex True (below inside row column) (rightOf inside row column))
              + Bool.toNat
                (concave True
                  (below inside row column)
                  (rightOf inside row column)
                  (below (rightOf inside) row column))))
      ]

--| `total` is the sum over `List.range`.
theorem totalRange ∀ (n: Nat) (f: Nat → Nat): (List.range 0 n).sumBy f = total n f := match n with
  | Zero => byComputing
  | Succ n => rewrite List.sumByRangeSucc f n, totalRange n (i => f (Succ i))

--| The square of the grid with rows and columns up to `last`, row by row.
def square (last: Nat): List Position :=
  List.range 0 (Succ last) |> .flatMap (row => List.range 0 (Succ last) |> .map (column => ({ row, column }: Position)))

theorem memSquare ∀ (last row column: Nat)
    (rowIn: row ≤ last)
    (columnIn: column ≤ last):
    ({ row, column }: Position) ∈ square last :=
  List.memFlatMapIntro
    (row => List.range 0 (Succ last) |> .map (column => ({ row, column }: Position)))
    row
    { row, column }
    (List.range 0 (Succ last))
    (List.memRangeFromIntro row (Succ last) 0 (arithmetic) (arithmetic))
    (List.memMap
      (List.range 0 (Succ last))
      column
      (List.memRangeFromIntro column (Succ last) 0 (arithmetic) (arithmetic))
      (column => ({ row, column }: Position)))

theorem squareDistinct ∀ (last: Nat): List.Distinct (square last) :=
  List.distinctFlatMap
    (row => List.range 0 (Succ last) |> .map (column => ({ row, column }: Position)))
    (position => position.row)
    (List.range 0 (Succ last))
    (List.distinctRangeFrom (Succ last) 0)
    (row inRows =>
      List.distinctMap
        (List.range 0 (Succ last))
        (List.distinctRangeFrom (Succ last) 0)
        (column => ({ row, column }: Position))
        (first second same => Eq.cong (position => position.column) same))
    (row inRows position member =>
      List.anyElim
        (column => ({ row, column }: Position) = position)
        (position.row = row)
        (List.range 0 (Succ last))
        (List.memMapAny (List.range 0 (Succ last)) (column => ({ row, column }: Position)) position member)
        (column inColumns built => rewrite <- built))

--| A sum over a region's plots, of something that is 0 off the region, is
--| the sum over a square of the grid that holds the region.
theorem sumOverGrid ∀ (region: Region)
    (distinct: List.Distinct region.plots) (last: Nat)
    (within: ∀ (plot: Position) => plot ∈ region.plots → (plot.row ≤ last) ∧ (plot.column ≤ last)) (f: Nat → Nat → Nat)
    (zero: ∀ (row column: Nat) => insideOf region row column = False → f row column = 0):
    region.plots.sumBy (plot => f plot.row plot.column)
      = total (Succ last) (row => total (Succ last) (column => f row column)) :=
  let isIn := (plot: Position) => region.contains plot
  let term := (plot: Position) => f plot.row plot.column
  let kept := (square last).filter isIn
  let same: List.Perm kept region.plots :=
    List.permOfSameMembers kept region.plots
      (List.distinctFilter (square last) isIn (squareDistinct last))
      distinct
      (plot member => (And.right (List.memFilter (square last) isIn member)).read)
      (plot member =>
        List.memFilterIntro
          (square last)
          isIn
          (match plot with
            | { row, column } =>
              let bounds := within { row, column } member
              memSquare last row column bounds.left bounds.right)
          member)
  let filtered :=
    Eq.trans
      (List.sumByFilter (square last) term isIn)
      (List.sumByCong (square last) (plot => if isIn plot then term plot else Add.zero) term (plot =>
        match plot with
          | { row, column } =>
            match found: insideOf region row column with
              | True => byComputing
              | False => (zero row column found).flipped))
  let bySquare := calc (square last).sumBy term
    _ = (List.range 0 (Succ last)).sumBy (row =>
        (List.range 0 (Succ last) |> .map (column => ({ row, column }: Position))).sumBy term) :=
      List.sumByFlatMap (List.range 0 (Succ last)) term (row =>
        List.range 0 (Succ last) |> .map (column => ({ row, column }: Position)))
    _ = (List.range 0 (Succ last)).sumBy (row => total (Succ last) (column => f row column)) :=
      List.sumByCong
        (List.range 0 (Succ last))
        (row => (List.range 0 (Succ last) |> .map (column => ({ row, column }: Position))).sumBy term)
        (row => total (Succ last) (column => f row column))
        (row =>
          Eq.trans
            (List.sumByMap (List.range 0 (Succ last)) term (column => ({ row, column }: Position)))
            (totalRange (Succ last) (column => f row column)))
    _ = total (Succ last) (row => total (Succ last) (column => f row column)) :=
      totalRange (Succ last) (row => total (Succ last) (column => f row column))
  calc region.plots.sumBy term
    _ = kept.sumBy term := Eq.flipped (List.sumByPerm kept region.plots same term)
    _ = (square last).sumBy term := filtered
    _ = total (Succ last) (row => total (Succ last) (column => f row column)) := bySquare

--| The program's count of a region's corners is the spec's count of its
--| sides.
theorem sidesCorrect ∀ (garden: Garden) (start: Position) (plant: Char)
    (grows: garden.plantAt start = Some plant) (region: Region)
    (isRegion: IsRegion garden start region)
    (distinct: List.Distinct region.plots):
    region.sides garden = sides region :=
  let inside := insideOf region
  let last := region.plots.sumBy (plot => plot.row + plot.column)
  let within := (plot: Position) =>
    (member: plot ∈ region.plots) =>
      let le := List.memLeSumBy (plot => plot.row + plot.column) region.plots plot member
      (Both (arithmetic [le]) (arithmetic [le]): (plot.row ≤ last) ∧ (plot.column ≤ last))
  let right: ∀ (row: Nat) => inside row (Succ last) = False := row =>
    match found: inside row (Succ last) with
      | False => byComputing
      | True => Void.impossible (arithmetic [And.right (within { row, column = Succ last } found.read)])
  let bottom: ∀ (column: Nat) => inside (Succ last) column = False := column =>
    match found: inside (Succ last) column with
      | False => byComputing
      | True => Void.impossible (arithmetic [And.left (within { row = Succ last, column } found.read)])
  let programSide :=
    Eq.trans
      (List.sumByCongMem region.plots garden.cornerCount (plot => corners inside plot.row plot.column) (plot member =>
        programCornersCell garden start plant grows region isRegion plot member))
      (sumOverGrid region distinct last within (row column => corners inside row column) (row column outside =>
        rewrite outside))
  let specSide :=
    Eq.trans
      (List.sumByCong region.plots
        (plot => directions.count (isFirstSection region plot))
        (plot => starts inside plot.row plot.column)
        (plot => match plot with | { row, column } => specSidesCell region row column))
      (sumOverGrid region distinct last within (row column => starts inside row column) (row column outside =>
        rewrite outside))
  calc region.sides garden
    _ = total (Succ last) (row => total (Succ last) (column => corners inside row column)) := programSide
    _ = total (Succ last) (row => total (Succ last) (column => starts inside row column)) :=
      cornersEqualSides inside last right bottom
    _ = sides region := specSide.flipped
