-- Rest patterns: `[a, b, ..rest]` is `Cons a (Cons b rest)`. `..` comes last
-- and is followed by any pattern (`rest`, `_`, even `[]`); `[..p]` is just `p`.

def describe : List Nat -> Text
  | [] => "empty"
  | [x] => "one"
  | [x, y, ..rest] => "two or more"

test "describeEmpty" := describe [] == "empty"
test "describeOne" := describe [1] == "one"
test "describeMany" := describe [1, 2, 3] == "two or more"

def sumTwo (xs : List Nat) : Nat :=
  match xs with
    | [a, b, .._] => a + b
    | _ => 0

test "sumTwoLong" := sumTwo [1, 2, 3, 4] == 3
test "sumTwoShort" := sumTwo [1] == 0

def tailOf : List Nat -> List Nat
  | [] => []
  | [_, ..rest] => rest

test "tailOf" := tailOf [1, 2, 3] == [2, 3]

-- `[..rest]` alone is `rest`.
def same : List Nat -> List Nat
  | [..xs] => xs

test "same" := same [4, 5] == [4, 5]

-- Nested in a tuple.
def pairHeads : (List Nat, List Nat) -> Nat
  | ([a, ..as], [b, ..bs]) => a + b
  | _ => 0

test "pairHeads" := pairHeads ([1, 2], [3]) == 4


theorem tailOfExample : tailOf [1, 2, 3] = [2, 3] := rfl
