-- `Array a` is for values you look up and update by position, many times.
-- It is not in the prelude: import it. (`xs.toArray` needs no import.)
import Std (Array)

-- A counter for each digit, updated in a loop. A list would walk to the
-- digit on every update; an array goes straight there.
def tally (digits: List Nat): Array Nat :=
  digits.foldLeft (Array.replicate (count := 10) 0) (counts digit => counts.modify digit (n => n + 1))

-- Looking up never fails loudly: `get` gives an Option, `getOr` a fallback.
test "counting" := (tally [3, 1, 3, 3]).toList == [0, 1, 0, 3, 0, 0, 0, 0, 0, 0]
test "get" := (tally [3]).get 3 == Some 1 ∧ (tally [3]).get 99 == None
test "getOr" := (tally [3]).getOr (index := 99) (fallback := 0) == 0

-- `getLt` needs a proof that the index is in range, which `auto` finds
-- from the check, so the answer is a plain number.
def lookup (counts: Array Nat) (digit: Nat): Nat := if digit < counts.size then counts.getLt digit else 0

test "in range" := lookup (tally [5, 5]) 5 == 2

-- Setting past the end leaves the array as it was.
test "out of range" := (tally [1]).set (index := 10) (value := 7) == tally [1]
