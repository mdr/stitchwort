-- Day 12 proved, for every map: the program's regions are the map's
-- regions, each plot in exactly one (`regionsAreRegions`, `inOneRegion`,
-- Regions.sw, from the flood fill's `regionOfIsRegion`, Fill.sw); and both
-- parts are the spec's total price over them, by perimeter
-- (`part1Correct`, through `perimeterCorrect`, Fences.sw) and by sides
-- (`part2Correct`, through `sidesCorrect`, Sides.sw, and
-- `cornersEqualSides`, Corners.sw).

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Exists, List, Nat)

-- Part 1: the program's total is the spec's total price over the
-- program's regions, which are the map's regions, each once
-- (`regionsAreRegions`, `inOneRegion`).
theorem part1Correct (garden: Garden): solvePart1 garden = totalPrice garden.regions perimeter :=
  sumByCongMem garden.regions (region => region.length * garden.perimeter region) (region => area region * perimeter region) (region member =>
    Exists.elim (regionsAreRegions garden region member) (start both =>
      Exists.elim (And.left both) (plant grows => rewrite perimeterCorrect garden start plant grows region (And.left (And.right both)) in rfl)))

-- Part 2: the program's total is the spec's total price, by sides, over
-- the program's regions.
theorem part2Correct (garden: Garden): solvePart2 garden = totalPrice garden.regions sides :=
  sumByCongMem garden.regions (region => region.length * garden.sides region) (region => area region * sides region) (region member =>
    Exists.elim (regionsAreRegions garden region member) (start both =>
      Exists.elim (And.left both) (plant grows =>
        rewrite sidesCorrect garden start plant grows region (And.left (And.right both)) (And.right (And.right both)) in rfl)))
