-- A turn as the seeded handler runs it is `resolve` with that seed's dice.
-- `step` performs `Random` exactly once, so the handler computes, and this
-- holds by `rfl`. It is why the invariants (Walls.sw, HitPoints.sw, Floor.sw,
-- Occupancy.sw) can be proved about the pure `resolve`, for every seed.

namespace Rogue.Proofs
import Rogue (..)

theorem seededStep (seed: Nat) (state: State) (command: Command):
    seeded seed (() => step state command) = resolve { seed = lcg seed / 65536 } state command :=
  rfl
