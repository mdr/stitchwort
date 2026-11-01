-- D2118, AoC 2021 day 17: number literals with no expected type (inferred,
-- inside tuples) are `Nat` at once, so `-4` fails.
import Std (Int, List, Nat)

type Velocity = { dx: Int, dy: Int }

def velocities: List Velocity := [(7, 2), (6, 3), (17, -4)].map (((dx, dy)) => { dx, dy })

test "negative kept" := velocities.map (v => v.dy) == [2, 3, -4]
