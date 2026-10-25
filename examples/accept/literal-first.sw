-- A literal in the first place takes its type from the rest of the call.
-- The value goes first (D303), so in `List.map [1, 2] (x => x): List Int`
-- the list is checked before the lambda that ties its elements to `Int`:
-- where checking it in place would settle them as `Nat` and fail, it's
-- checked after the later arguments instead, as a constructor with a number
-- in it is. The dot and pipe forms are the same call.

import Std (Int, List)

def prefixForm: List Int := List.map [1, 2] (x => x)
def dotForm: List Int := [1, 2].map (x => x)
def pipeForm: List Int := [1, 2] |> List.map (x => x)

-- A number on the left of a pipe too: `5 |> Int.sub 7` is `Int.sub 5 7`.
def numberPipe: Int := 5 |> Int.sub 7

-- Other arguments come between: the initial value is an `Int` once the
-- expected type says so, and the list follows.
def summed: Int := List.foldLeft [1, 2] 0 (acc x => acc + x)
def nested: List (List Int) := [[1], [2, 3]].map (xs => xs)

-- Where checking in place works, it's what happens: `x + 1` needs `x`'s
-- type, which the list gives.
def plain: List Nat := List.map [1, 2] (x => x + 1)

test "prefix" := prefixForm == [1, 2]
test "dot" := dotForm == [1, 2]
test "pipe" := pipeForm == [1, 2]
test "number pipe" := numberPipe == -2
test "summed" := summed == 3
test "nested" := nested == [[1], [2, 3]]
test "plain" := plain == [2, 3]
