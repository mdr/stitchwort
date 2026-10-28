-- Part 2: the program counts a region's corners, the spec its sides, and
-- the two agree for every region (`sidesCorrect`), through the grid of
-- booleans of Corners.sw: the program's corners at a plot are the grid's
-- (`programCornersCell`), the spec's first sections of fence the grid's
-- starts (`specSidesCell`), and a sum over the region's plots is a sum over
-- a square of the grid big enough to hold it (`sumOverGrid`).

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Nat, Option, Or, Void)

-- The region as a grid of booleans.
def insideOf (region: List Position) (row: Nat) (column: Nat): Bool := region.any (member => member == ({ row, column }: Position))

theorem countDirections (f: Direction → Bool): directions.count f = Bool.toNat (f Up) + Bool.toNat (f Down) + Bool.toNat (f Left) + Bool.toNat (f Right) :=
  rewrite List.countCons [Down, Left, Right] Up f, List.countCons [Left, Right] Down f, List.countCons [Right] Left f, List.countCons Nil Right f in omega

theorem countQuadrants (f: (Direction, Direction) → Bool):
    quadrants.count f = Bool.toNat (f (Up, Left)) + Bool.toNat (f (Up, Right)) + Bool.toNat (f (Down, Left)) + Bool.toNat (f (Down, Right)) :=
  rewrite List.countCons [(Up, Right), (Down, Left), (Down, Right)] (Up, Left) f, List.countCons [(Down, Left), (Down, Right)] (Up, Right) f,
    List.countCons [(Down, Right)] (Down, Left) f, List.countCons Nil (Down, Right) f in omega

-- The spec's first sections of fence at a plot are the grid's starts.
theorem specSidesCell (region: List Position): (row: Nat) → (column: Nat) →
    directions.count (isFirstSection region { row, column }) = starts (insideOf region) row column
  | Zero, Zero => Eq.trans (countDirections (isFirstSection region _)) rfl
  | Zero, Succ before => Eq.trans (countDirections (isFirstSection region _)) rfl
  | Succ up, Zero => Eq.trans (countDirections (isFirstSection region _)) rfl
  | Succ up, Succ before => Eq.trans (countDirections (isFirstSection region _)) rfl

-- Each side of a plot touches the region where the grid's neighbour is in.
theorem facesUp (region: List Position): (row: Nat) → (column: Nat) → facesRegion region { row, column } Up = above (insideOf region) row column
  | Zero, column => rfl
  | Succ up, column => rfl

theorem facesDown (region: List Position) (row: Nat) (column: Nat): facesRegion region { row, column } Down = below (insideOf region) row column := rfl

theorem facesLeft (region: List Position): (row: Nat) → (column: Nat) → facesRegion region { row, column } Left = leftOf (insideOf region) row column
  | row, Zero => rfl
  | row, Succ before => rfl

theorem facesRight (region: List Position) (row: Nat) (column: Nat): facesRegion region { row, column } Right = rightOf (insideOf region) row column := rfl

-- Whether the plot diagonally across a corner, one step `vertical` then one
-- `horizontal`, is in the region.
def diagonalIn (region: List Position) (plot: Position) (vertical: Direction) (horizontal: Direction): Bool :=
  match plot.step vertical with
    | Some next => facesRegion region next horizontal
    | None => False

theorem diagonalUpLeft (region: List Position): (row: Nat) → (column: Nat) →
    diagonalIn region { row, column } Up Left = above (leftOf (insideOf region)) row column
  | Zero, column => rfl
  | Succ up, Zero => rfl
  | Succ up, Succ before => rfl

theorem diagonalUpRight (region: List Position): (row: Nat) → (column: Nat) →
    diagonalIn region { row, column } Up Right = above (rightOf (insideOf region)) row column
  | Zero, column => rfl
  | Succ up, column => rfl

theorem diagonalDownLeft (region: List Position): (row: Nat) → (column: Nat) →
    diagonalIn region { row, column } Down Left = below (leftOf (insideOf region)) row column
  | row, Zero => rfl
  | row, Succ before => rfl

theorem diagonalDownRight (region: List Position) (row: Nat) (column: Nat):
    diagonalIn region { row, column } Down Right = below (rightOf (insideOf region)) row column := rfl

-- `!=` is `!` of `==`.
theorem notEqualNot (x: Option Char) (y: Option Char): ((x != y): Bool) = Bool.not (x == y) :=
  match decision: DecEq.decide x y with
    | Yes same => rfl
    | No differ => rfl

-- Where a side of a plot in a region faces the same plant, the plot
-- diagonally across grows another exactly when it isn't in the region.
theorem diagonalSame (garden: Garden) (start: Position) (plant: Char) (grows: garden.plantAt start = Some plant) (region: List Position)
    (isRegion: IsRegion garden start region) (plot: Position) (member: plot ∈ region) (vertical: Direction) (horizontal: Direction)
    (same: garden.sameAcross plot vertical = True):
    (((plot.diagonal vertical horizontal |> .flatMap garden.plantAt) != garden.plantAt plot): Bool) = Bool.not (diagonalIn region plot vertical horizontal) :=
  let plotGrows := joinedPlant garden plant start plot grows ((isRegion plot).forward member)
  let faces := Eq.trans (Eq.sym (sameAcrossFaces garden start plant grows region isRegion plot member vertical)) same
  match stepped: plot.step vertical with
    | None => Void.exfalso (Bool.falseNotTrue faces)
    | Some next =>
      let nextIn := (anyEqual region next).forward faces
      let nextGrows := joinedPlant garden plant start next grows ((isRegion next).forward nextIn)
      rewrite notEqualNot, plotGrows, <- sameAcrossFaces garden start plant grows region isRegion next nextIn horizontal, nextGrows in rfl

-- A corner of the program's, split into outside and inside.
theorem isCornerSplit (garden: Garden) (plot: Position) (vertical: Direction) (horizontal: Direction) (verticalIn: Bool) (horizontalIn: Bool)
    (diagonal: Bool) (verticalSame: garden.sameAcross plot vertical = verticalIn) (horizontalSame: garden.sameAcross plot horizontal = horizontalIn)
    (across: verticalIn = True → (((plot.diagonal vertical horizontal |> .flatMap garden.plantAt) != garden.plantAt plot): Bool) = Bool.not diagonal):
    Bool.toNat (garden.isCorner plot vertical horizontal)
      = Bool.toNat (convex True verticalIn horizontalIn) + Bool.toNat (concave True verticalIn horizontalIn diagonal) :=
  rewrite verticalSame, horizontalSame in
    match verticalIn, horizontalIn with
      | False, False => rfl
      | False, True => rfl
      | True, False => rfl
      | True, True =>
        rewrite across rfl in
          match diagonal with
            | True => rfl
            | False => rfl

-- The program's corners at a plot of a region are the grid's.
theorem programCornersCell (garden: Garden) (start: Position) (plant: Char) (grows: garden.plantAt start = Some plant) (region: List Position)
    (isRegion: IsRegion garden start region): (plot: Position) → plot ∈ region → garden.cornerCount plot = corners (insideOf region) plot.row plot.column
  | { row, column }, member =>
    let plot: Position := { row, column }
    let inside := insideOf region
    let isIn: inside row column = True := (anyEqual region plot).backward member
    let faces := (side: Direction) => sameAcrossFaces garden start plant grows region isRegion plot member side
    let up := Eq.trans (faces Up) (facesUp region row column)
    let down := Eq.trans (faces Down) (facesDown region row column)
    let left := Eq.trans (faces Left) (facesLeft region row column)
    let right := Eq.trans (faces Right) (facesRight region row column)
    let diagonal := (vertical: Direction) => (horizontal: Direction) => (same: garden.sameAcross plot vertical = True) =>
      diagonalSame garden start plant grows region isRegion plot member vertical horizontal same
    omega [
      countQuadrants (quadrant => garden.isCorner plot quadrant.fst quadrant.snd),
      isCornerSplit garden plot Up Left (above inside row column) (leftOf inside row column) (above (leftOf inside) row column) up left
        (same => rewrite <- diagonalUpLeft region row column in diagonal Up Left (Eq.trans up same)),
      isCornerSplit garden plot Up Right (above inside row column) (rightOf inside row column) (above (rightOf inside) row column) up right
        (same => rewrite <- diagonalUpRight region row column in diagonal Up Right (Eq.trans up same)),
      isCornerSplit garden plot Down Left (below inside row column) (leftOf inside row column) (below (leftOf inside) row column) down left
        (same => rewrite <- diagonalDownLeft region row column in diagonal Down Left (Eq.trans down same)),
      isCornerSplit garden plot Down Right (below inside row column) (rightOf inside row column) (below (rightOf inside) row column) down right
        (same => rewrite <- diagonalDownRight region row column in diagonal Down Right (Eq.trans down same)),
      (rewrite isIn in rfl: corners inside row column
        = Bool.toNat (convex True (above inside row column) (leftOf inside row column))
          + Bool.toNat (concave True (above inside row column) (leftOf inside row column) (above (leftOf inside) row column))
          + (Bool.toNat (convex True (above inside row column) (rightOf inside row column))
            + Bool.toNat (concave True (above inside row column) (rightOf inside row column) (above (rightOf inside) row column)))
          + (Bool.toNat (convex True (below inside row column) (leftOf inside row column))
            + Bool.toNat (concave True (below inside row column) (leftOf inside row column) (below (leftOf inside) row column)))
          + (Bool.toNat (convex True (below inside row column) (rightOf inside row column))
            + Bool.toNat (concave True (below inside row column) (rightOf inside row column) (below (rightOf inside) row column))))
    ]

-- `total` is the sum over `List.range`.
theorem totalRange: (n: Nat) → (f: Nat → Nat) → (List.range n).sumBy f = total n f
  | Zero, f => rfl
  | Succ n, f => rewrite List.sumByRangeSucc f n, totalRange n (i => f (Succ i)) in rfl

-- A member's term is at most the sum.
theorem memLeSumBy (f: a → Nat): (xs: List a) → (x: a) → x ∈ xs → f x ≤ xs.sumBy f
  | Nil, x, none => Void.exfalso none
  | Cons first rest, x, Inl same => rewrite List.sumByCons rest first f, same in omega
  | Cons first rest, x, Inr later => rewrite List.sumByCons rest first f in omega [memLeSumBy f rest x later]

-- The square of the grid with rows and columns up to `last`, row by row.
def square (last: Nat): List Position :=
  List.range (Succ last) |> .flatMap (row => List.range (Succ last) |> .map (column => ({ row, column }: Position)))

theorem memSquare (last: Nat) (row: Nat) (column: Nat) (rowIn: row ≤ last) (columnIn: column ≤ last): ({ row, column }: Position) ∈ square last :=
  List.memFlatMapIntro (row => List.range (Succ last) |> .map (column => ({ row, column }: Position))) row { row, column } (List.range (Succ last))
    (List.memRangeFromIntro row (Succ last) 0 (omega) (omega))
    (List.memMap (List.range (Succ last)) column (List.memRangeFromIntro column (Succ last) 0 (omega) (omega)) (column => ({ row, column }: Position)))

theorem squareDistinct (last: Nat): List.Distinct (square last) :=
  List.distinctFlatMap (row => List.range (Succ last) |> .map (column => ({ row, column }: Position))) (position => position.row)
    (List.range (Succ last)) (List.distinctRangeFrom (Succ last) 0)
    (row inRows =>
      List.distinctMap (List.range (Succ last)) (List.distinctRangeFrom (Succ last) 0) (column => ({ row, column }: Position))
        (first second same => Eq.cong (position => position.column) same))
    (row inRows position member =>
      List.anyElim (column => ({ row, column }: Position) = position) (position.row = row) (List.range (Succ last))
        (List.memMapAny (List.range (Succ last)) (column => ({ row, column }: Position)) position member)
        (column inColumns built => rewrite <- built in rfl))

-- A sum over a region's plots, of something that is 0 off the region, is
-- the sum over a square of the grid that holds the region.
theorem sumOverGrid (region: List Position) (distinct: List.Distinct region) (last: Nat)
    (within: (plot: Position) → plot ∈ region → And (plot.row ≤ last) (plot.column ≤ last)) (f: Nat → Nat → Nat)
    (zero: (row: Nat) → (column: Nat) → insideOf region row column = False → f row column = 0):
    region.sumBy (plot => f plot.row plot.column) = total (Succ last) (row => total (Succ last) (column => f row column)) :=
  let isIn := (plot: Position) => region.any (member => member == plot)
  let term := (plot: Position) => f plot.row plot.column
  let kept := (square last).filter isIn
  let same: List.Perm kept region :=
    List.permOfSameMembers kept region (List.distinctFilter (square last) isIn (squareDistinct last)) distinct
      (plot member => (anyEqual region plot).forward (And.right (List.memFilter (square last) isIn plot member)))
      (plot member =>
        List.memFilterIntro (square last) isIn plot
          (match plot with
            | { row, column } =>
              let bounds := within { row, column } member
              memSquare last row column (And.left bounds) (And.right bounds))
          ((anyEqual region plot).backward member))
  let filtered :=
    Eq.trans (List.sumByFilter (square last) term isIn)
      (List.sumByCong (square last) (plot => if isIn plot then term plot else Add.zero) term (plot =>
        match plot with
          | { row, column } =>
            match found: insideOf region row column with
              | True => rfl
              | False => Eq.sym (zero row column found)))
  let bySquare :=
    Eq.trans (List.sumByFlatMap (List.range (Succ last)) term (row => List.range (Succ last) |> .map (column => ({ row, column }: Position))))
      (Eq.trans
        (List.sumByCong (List.range (Succ last)) (row => (List.range (Succ last) |> .map (column => ({ row, column }: Position))).sumBy term)
          (row => total (Succ last) (column => f row column)) (row =>
          Eq.trans (List.sumByMap (List.range (Succ last)) term (column => ({ row, column }: Position))) (totalRange (Succ last) (column => f row column))))
        (totalRange (Succ last) (row => total (Succ last) (column => f row column))))
  Eq.trans (Eq.sym (List.sumByPerm kept region same term)) (Eq.trans filtered bySquare)

-- The program's count of a region's corners is the spec's count of its
-- sides.
theorem sidesCorrect (garden: Garden) (start: Position) (plant: Char) (grows: garden.plantAt start = Some plant) (region: List Position)
    (isRegion: IsRegion garden start region) (distinct: List.Distinct region): garden.sides region = sides region :=
  let inside := insideOf region
  let last := region.sumBy (plot => plot.row + plot.column)
  let within := (plot: Position) => (member: plot ∈ region) =>
    let le := memLeSumBy (plot => plot.row + plot.column) region plot member
    (Both (omega [le]) (omega [le]): And (plot.row ≤ last) (plot.column ≤ last))
  let right: (row: Nat) → inside row (Succ last) = False := row =>
    match found: inside row (Succ last) with
      | False => rfl
      | True => Void.exfalso (omega [And.right (within { row, column = Succ last } ((anyEqual region { row, column = Succ last }).forward found))])
  let bottom: (column: Nat) → inside (Succ last) column = False := column =>
    match found: inside (Succ last) column with
      | False => rfl
      | True => Void.exfalso (omega [And.left (within { row = Succ last, column } ((anyEqual region { row = Succ last, column }).forward found))])
  let programSide :=
    Eq.trans
      (sumByCongMem region garden.cornerCount (plot => corners inside plot.row plot.column)
        (plot member => programCornersCell garden start plant grows region isRegion plot member))
      (sumOverGrid region distinct last within (row column => corners inside row column) (row column outside => rewrite outside in rfl))
  let specSide :=
    Eq.trans
      (List.sumByCong region (plot => directions.count (isFirstSection region plot)) (plot => starts inside plot.row plot.column) (plot =>
        match plot with
          | { row, column } => specSidesCell region row column))
      (sumOverGrid region distinct last within (row column => starts inside row column) (row column outside => rewrite outside in rfl))
  Eq.trans programSide (Eq.trans (cornersEqualSides inside last right bottom) (Eq.sym specSide))
