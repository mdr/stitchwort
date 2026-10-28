-- Adds functions to P's `Grid` and to its nickname `Area`; they are
-- `P.Spec.Grid.probe` and `P.Spec.Area.cells`.
namespace P.Spec

import P (Grid, Area)

def Grid.probe (grid: Grid): Nat := grid.width + 1

def Area.cells (area: Area): Nat := area.width * 2

def Grid.twice (grid: Grid): Nat := 2

def sample: Grid := { width = 3 }

test "dot" := sample.probe == 4
test "the type's own" := sample.size == 3
test "qualified" := Grid.probe sample == 4
test "full name" := P.Spec.Grid.probe sample == 4
test "section" := [sample].map .probe == [4]
test "nickname" := (sample: Area).cells == 6
test "through a nickname" := (sample: Area).probe == 4
