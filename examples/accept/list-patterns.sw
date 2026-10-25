-- List patterns: `[]` is `Nil` and `[p, q]` is `Cons p (Cons q Nil)`, the
-- library's constructors by identity.

-- Equations, with a fallback.
def describe: List Nat → Nat
  | [] => 0
  | [x] => x
  | [x, y] => x + y
  | _ => 100

test "describeEmpty" := describe [] == 0
test "describeOne" := describe [7] == 7
test "describeTwo" := describe [3, 4] == 7
test "describeMany" := describe [1, 2, 3] == 100

-- `match`, with an ordinary constructor pattern as the last resort.
def firstTwo (xs: List Nat): Nat :=
  match xs with
    | [] => 0
    | [a, b] => a * b
    | Cons a _ => a

test "firstTwoPair" := firstTwo [3, 4] == 12
test "firstTwoLonger" := firstTwo [5, 6, 7] == 5

-- A list in a tuple, and a tuple in a list.
def pick: (List Nat, List Nat) → Nat
  | (xs, [y]) => y
  | ([], _) => 1
  | _ => 2

test "pickOne" := pick ([1, 2], [9]) == 9
test "pickEmpty" := pick ([], [1, 2]) == 1
test "pickOther" := pick ([1], [1, 2]) == 2

def sumPair: List (Nat, Nat) → Nat
  | [(a, b)] => a + b
  | _ => 0

test "sumPairOne" := sumPair [(1, 2)] == 3

-- Nested lists, and a constructor element (no brackets needed).
def nested: List (List Nat) → Nat
  | [[a], [b, c]] => a + b + c
  | _ => 0

test "nestedTwo" := nested [[1], [2, 3]] == 6

def justs: List (Option Nat) → Nat
  | [Some a, None] => a
  | _ => 0

test "justsOne" := justs [Some 4, None] == 4

-- `let` and lambda patterns must cover their type, and no list pattern does
-- (see reject/list-pattern-let-refutable.sw), so lists go in `match`.
-- `match` in a lambda body.
def lengthOne: List Nat → Nat := xs => match xs with
  | [_] => 1
  | _ => 0

test "lengthOneYes" := lengthOne [3] == 1
test "lengthOneNo" := lengthOne [] == 0
