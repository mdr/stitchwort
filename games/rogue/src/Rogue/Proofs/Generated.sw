-- Proofs about the generator's randomness under the seeded handler.
--
-- The generator rolls as it goes (`let down := 2 + roll 3`), for
-- readability, so nothing here follows a whole level through the handler:
-- what is proved about levels is proved for any rooms (`goalReachable`,
-- Reach.sw; `roomFits` and `layOutFramed`, Bounds.sw). See PROOFS.md §3.

namespace Rogue.Proofs
import Rogue (..)
import Std (Nat)

-- A roll is below its bound: `roll most` under the seeded handler is at
-- most `most`. (Under any handler, `roll most` is a remainder by
-- `Succ most`; `seeded` is the handler the game and its tests use.)
theorem rollBelow (seed: Nat) (most: Nat): seeded seed (() => roll most) < Succ most := Nat.modLt (lcg seed / 65536) (Succ most)
