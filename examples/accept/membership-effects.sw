-- `x in c` and `x !in c` where a part performs operations, or may: inside
-- the callback of an effect-polymorphic `List.filter` or `List.all`, the
-- container `List.map xs f` is a computation in the callback's row. The
-- element runs first, then the container, and where a `Bool` is expected
-- the membership is decided, as it is with nothing to run (SW-573). So are
-- `<`, `=` and `!=` there.

import Std (List)

-- The motivating shapes: a `map` on the right, in a filter's callback.
def shifted (xs: List Nat) (ys: List Nat): List Nat :=
  List.filter ys (y => y ∈ List.map xs (n => n + 1))

def notShifted (xs: List Nat) (ys: List Nat): List Nat :=
  List.filter ys (y => y ∉ List.map xs (n => n + 1))

def allShifted (xs: List Nat) (ys: List Nat): Bool :=
  List.all ys (y => y ∈ List.map xs (n => n + 1))

-- The first list, then the second's items whose key isn't among the first's.
def joinByKey (key: a → b) (xs: List a) (ys: List a) [auto eq: DecEq b]: List a :=
  xs ++ ys.filter (y => key y ∉ xs.map key)

-- A comparison with a computed side, and `!` of one.
def belowLength (xs: List Nat) (ys: List Nat): List Nat :=
  List.filter ys (y => y < List.length (List.map xs (n => n + 1)))

def notBelowLength (xs: List Nat) (ys: List Nat): List Nat :=
  List.filter ys (y => !(y < List.length (List.map xs (n => n + 1))))

def otherThanLength (xs: List Nat) (ys: List Nat): List Nat :=
  List.filter ys (y => List.length (List.map xs (n => n + 1)) != y)

-- With operations to perform: the element runs before the container.
ability Log where
  say: Nat → {Log} ()

def collect (prog: () → {Log | e} a): {e} Pair (List Nat) a :=
  handle prog() with
    | return x => MkPair Nil x
    | say n, k =>
      let rest := k()
      MkPair (Cons n rest.fst) rest.snd

def loud (n: Nat): {Log} Nat :=
  say n
  n

def loudList (xs: List Nat): {Log} List Nat :=
  say 100
  xs

def loudMember(): {Log} Bool := loud 2 ∈ loudList [1, 2, 3]

def loudNotMember(): {Log} Bool := loud 2 ∉ loudList [1, 3]

test "in a map, in a filter" := shifted [1, 2] [2, 5, 3] == [2, 3]
test "not in a map, in a filter" := notShifted [1, 2] [2, 5, 3] == [5]
test "in a map, in all" := allShifted [1, 2] [3, 2] ∧ not (allShifted [1, 2] [4])
test "join by key" := joinByKey (n => n % 10) [1, 12] [21, 3, 32] == [1, 12, 3]
test "comparison" := belowLength [7, 8] [0, 2, 1] == [0, 1]
test "not a comparison" := notBelowLength [7, 8] [0, 2, 1] == [2]
test "not equal" := otherThanLength [7, 8] [0, 2, 1] == [0, 1]
test "the element runs first" := collect loudMember == MkPair [2, 100] True
test "not in, the element first" := collect loudNotMember == MkPair [2, 100] True
