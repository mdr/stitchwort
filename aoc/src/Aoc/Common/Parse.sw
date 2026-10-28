-- Pieces of puzzle-input grammars shared between days, for `Std.Parse`.

namespace Aoc.Common
import Std (Parse)
import Std.Parse (nat, spaces)

-- A number, with spaces allowed around it: " 12 " is 12.
def spacedNat(): {Parse} Nat :=
  spaces()
  let number := nat()
  spaces()
  number
