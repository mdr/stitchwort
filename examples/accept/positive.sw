-- Pairs with soundness/non-positive.sw: the type may appear as a field, or as
-- the *result* of a function field.
type Stream: Type =
  | MkStream (head: Nat) (rest: Nat -> Stream)

type Tree: Type =
  | Leaf
  | Node (left: Tree) (right: Tree)
