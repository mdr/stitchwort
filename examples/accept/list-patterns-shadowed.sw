-- A user's own `Nil` and `Cons` don't change what a list pattern means: it
-- is the library's `List`, by identity.
type Chain = | Nil | Cons (n: Nat) (rest: Chain)

def chainLength: Chain → Nat
  | Nil => 0
  | Cons _ rest => 1 + chainLength rest

def firstOfList: List Nat → Nat
  | [x, y] => x
  | _ => 0

test "own constructors" := chainLength (Cons 1 (Cons 2 Nil)) == 2
test "list patterns are the library's" := firstOfList [8, 9] == 8
