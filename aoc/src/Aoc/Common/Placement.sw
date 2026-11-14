--| What `assign` finds, read as a function on the positions. `assign`
--| gives the values in the order of the positions; a spec that says "the
--| value at each position" wants a function from a position to its value.
--| The proofs are in `Aoc.Common.Proofs` (Proofs/Placement.sw).

namespace Aoc.Common
import Std (DecEq, List)

--| The value at `key`'s place in `keys`, in `values`; `fallback` when `key`
--| is not among the keys, or the lists are of different lengths.
def valueAt [auto eq: DecEq k] (fallback: v): (keys: List k) → (values: List v) → (key: k) → v
  | [first, ..rest], [value, ..values], key => if key == first then value else valueAt fallback rest values key
  | _, _, key => fallback
