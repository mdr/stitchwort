-- Advent of Code 2025, day 4: a grid of paper rolls (@) and empty floor (.).
-- A roll is accessible when fewer than four of its eight neighbours are
-- rolls. Part 1 counts the accessible rolls. Part 2 removes them, repeats
-- until none are accessible, and counts every roll removed.
--
--   $ stitchwort run aoc/day04.sw < aoc/inputs/day04.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- The grid is a list of rows of 0 (floor) and 1 (roll). A roll's "window" is
-- the 3 by 3 block around it, itself included, so it is accessible when its
-- window holds fewer than 5 rolls. Sum each row horizontally in threes once,
-- then add the sums of the rows above, at, and below to get every window.

type Grid = List (List Nat)

def main () : {IO} () :=
  let grid := parseGrid (IO.readAllLines ())
  print ("Part 1: " ++ (solvePart1 grid).toText)
  print ("Part 2: " ++ (solvePart2 grid).toText)

-- Part 1: the rolls one round removes.
def solvePart1 (grid : Grid) : Nat := grid.rolls - grid.round.rolls

-- Part 2: the rolls removed by rounds until none is accessible.
def solvePart2 (grid : Grid) : Nat := grid.rolls - (grid.settle grid.rolls).rolls

def parseGrid (lines : List Text) : Grid := lines.map parseLine

def parseLine (line : Text) : List Nat := line.toList.map parseChar

-- A roll is 1, floor is 0.
def parseChar : Char -> Nat
  | '@' => 1
  | _   => 0

def Grid.rolls (grid : Grid) : Nat := grid |> .sumBy List.sum

-- Remove every accessible roll, all at once.
def Grid.round (grid : Grid) : Grid :=
  let sums := grid.map rowSums
  let gap := List.replicate ((grid.headOr []).length) 0
  let above := Cons gap sums
  let below := sums.drop 1 |> .append [gap]
  let windows := Grid.zipWith Nat.add (Grid.zipWith Nat.add above sums) below
  Grid.zipWith (\roll window => if roll == 1 && 5 <= window then 1 else 0) grid windows

-- Remove accessible rolls until there are none. Every round that changes
-- something removes a roll, so as many rounds as there are rolls is enough.
def Grid.settle (grid : Grid) : Nat -> Grid
  | Zero   => grid
  | Succ n =>
    let next := grid.round
    if next.rolls == grid.rolls then grid else next.settle n

-- Each cell becomes the sum of itself and its left and right neighbours.
def rowSums (row : List Nat) : List Nat :=
  let left := Cons 0 row
  let right := row.drop 1 |> .append [0]
  List.zipWith Nat.add (List.zipWith Nat.add left row) right

-- Combine two grids of the same shape cell by cell.
def Grid.zipWith (f : Nat -> Nat -> Nat) (a b : Grid) : Grid := List.zipWith (List.zipWith f) a b

-- Examples -----------------------------------------------------------------

def example : List Text :=
  [ "..@@.@@@@.", "@@@.@.@.@@", "@@@@@.@.@@", "@.@@@@..@.", "@@.@@@@.@@",
    ".@@@@@@@.@", ".@.@.@.@@@", "@.@@@.@@@@", ".@@@@@@@@.", "@.@.@@@.@." ]

test "example" := (solvePart1 (parseGrid example), solvePart2 (parseGrid example)) == (13, 43)
test "rolls" := (parseGrid example).rolls == 71
test "row sums" := rowSums [1, 0, 1, 1] == [1, 2, 2, 2]
test "lone roll" := (solvePart1 [[1]], solvePart2 [[1]]) == (1, 1)
test "full square" := (solvePart1 [[1, 1], [1, 1]], solvePart2 [[1, 1], [1, 1]]) == (4, 4)
def plus : Grid := [[0, 1, 0], [1, 1, 1], [0, 1, 0]]

test "plus shape keeps its centre" := (solvePart1 plus, solvePart2 plus) == (4, 5)

