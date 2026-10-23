-- `Option a` is `Some value` or `None`: how a lookup says "not found",
-- instead of null or an exception.
def firstEven (xs: List Nat): Option Nat := xs.find (n => n % 2 == 0)

def doubled (xs: List Nat): Option Nat := firstEven xs |> .map (n => n * 2)

-- The common list functions are dot calls on a list.
def scores: List Nat := [3, 8, 5, 12]

def summary: Text :=
  let big := scores.filter (n => n > 4)
  "${big.length} big scores, total ${big.sum}, best ${scores.maximum}"

test "found" := firstEven scores == Some 8
test "not found" := firstEven [1, 3] == None
test "map" := doubled scores == Some 16
test "fallback" := (firstEven [1, 3]).getOrElse 0 == 0
test "summary" := summary == "3 big scores, total 25, best Some 12"
