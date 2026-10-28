-- An unrelated namespace adds its own `Grid.probe`: no clash, since no file
-- sees both.
namespace Q

import P (Grid)

def Grid.probe (grid: Grid): Nat := grid.width + 100

def sample: Grid := { width = 3 }

test "its own" := sample.probe == 103
test "P.Spec's, in full" := P.Spec.Grid.probe sample == 4
