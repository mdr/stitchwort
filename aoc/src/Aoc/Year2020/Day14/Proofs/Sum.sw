--| The spec's sum of memory names one number: two lists of distinct
--| addresses that both include every address not holding 0 sum to the same.

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Void)

theorem sumOfMemoryUnique (memory: Spec.Memory) (first: Nat) (second: Nat) (isFirst: Spec.SumOfMemory memory first)
    (isSecond: Spec.SumOfMemory memory second): first = second := match isFirst with
      | Witness xs (Both distinctX (Both coversX sumX)) =>
        match isSecond with
          | Witness ys (Both distinctY (Both coversY sumY)) =>
            rewrite sumX, sumY in
              List.sumByDistinctNonzero memory xs ys distinctX distinctY (address nonzero member => coversY address nonzero)
                (address nonzero member => coversX address nonzero)
