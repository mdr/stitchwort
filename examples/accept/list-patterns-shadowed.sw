-- A user's own `Nil` and `Cons` don't change what a list pattern means: it
-- is the library's `List`, by identity.
type Chain = | Nil | Cons (n : Nat) (rest : Chain)

chainLength : Chain -> Nat
chainLength Nil = 0
chainLength (Cons _ rest) = 1 + chainLength rest

firstOfList : List Nat -> Nat
firstOfList [x, y] = x
firstOfList _ = 0

test "own constructors" = chainLength (Cons 1 (Cons 2 Nil)) == 2
test "list patterns are the library's" = firstOfList [8, 9] == 8
