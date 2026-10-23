-- Pairs with reject/non-terminating.sw: recursion on a sub-part is accepted,
-- including on the second parameter and through two levels of matching.
def double: Nat -> Nat
  | Zero => Zero
  | Succ n => Succ (Succ (double n))

def addRight (m: Nat): Nat -> Nat
  | Zero => m
  | Succ n => Succ (addRight m n)

type Tree: Type =
  | Leaf
  | Node (left: Tree) (right: Tree)

def size: Tree -> Nat
  | Leaf => 1
  | Node l r => size l + size r
