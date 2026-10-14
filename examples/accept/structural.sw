-- Pairs with reject/non-terminating.sw: recursion on a sub-part is accepted,
-- including on the second parameter and through two levels of matching.
double : Nat -> Nat
double Zero     = Zero
double (Succ n) = Succ (Succ (double n))

addRight : Nat -> Nat -> Nat
addRight m Zero     = m
addRight m (Succ n) = Succ (addRight m n)

type Tree : Type =
  | Leaf
  | Node (left : Tree) (right : Tree)

size : Tree -> Nat
size Leaf         = 1
size (Node l r) = size l + size r
