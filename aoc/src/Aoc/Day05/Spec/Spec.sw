-- Day 5, part 2 as the puzzle states it, by brute force: the ids, up to the
-- largest end of a range, that some fresh range holds. The proof
-- (Proofs/Part2.sw) and the test (Tests/Spec.sw) compare the program's merge
-- with it.

namespace Aoc.Day05.Spec
import Aoc.Common (..)
import Aoc.Day05 (..)
import Std (List, Nat)

-- Part 2 as the puzzle says it, by brute force: the ids, up to the largest
-- end of a range, that some fresh range holds.
def countFresh (db: Database): Nat :=
  let top := db.fresh.foldLeft 0 (m r => Nat.max m r.to)
  List.range (top + 1) |> .count (id => db.fresh.any (r => r.contains id))
