--| The program's memory, a `Map` holding what was written, against the
--| spec's, a function: reading an address not written gives 0, a write
--| changes what it wrote and nothing else, and the sum of the map's values is
--| the sum over its keys, which are distinct and include every address not
--| holding 0.

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14 (Spec)
import Std (Bool, DecEq, Eq, List, Map, Nat, Option, Pair, Void)

--| A memory the map describes sums to the sum of the map's values.
theorem sumOfMap ∀ (memory: Map Nat Nat) (spec: Spec.Memory)
    (same: ∀ (address: Nat) => spec address = memory.getOr address 0):
    Spec.SumOfMemory spec memory.values.sum :=
  let covered := (address: Nat) (nonzero: spec address ≠ 0) =>
    match found: memory.get address with
      | Some value => (Map.memKeys memory address).backward (Map.containsOfGet memory address value found)
      | None => Void.exfalso (nonzero (Eq.trans (same address) (rewrite found in rfl)))
  let summed: memory.values.sum = memory.keys.sumBy spec := Map.sumValuesEqSumByKeys memory spec same
  Witness memory.keys (Both (Map.keysDistinct memory) (Both covered summed))
