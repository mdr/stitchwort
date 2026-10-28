-- Sees P.Spec's functions through `(..)`; its own `Grid.twice` comes before
-- P.Spec's.
namespace P.Proofs

import P (Grid)
import P.Spec (..)

def Grid.twice (grid: Grid): Nat := 20

test "imported" := sample.probe == 4
test "own first" := sample.twice == 20
test "own first, qualified" := Grid.twice sample == 20
test "imported, in full" := P.Spec.Grid.twice sample == 2

theorem probeIsSucc (grid: Grid): grid.probe = grid.width + 1 := rfl
