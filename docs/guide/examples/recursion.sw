-- Chapter 7: recursion and termination.
import Std (List, Nat, Text)

-- begin structural
def length: List a -> Nat
  | [] => 0
  | Cons _ rest => 1 + length rest

def factorial: Nat -> Nat
  | 0 => 1
  | Succ n => Succ n * factorial n

test "structural" := length [1, 2, 3] == 3 && factorial 5 == 120
-- end structural

-- begin accumulator
def reverseOnto (done: List a): List a -> List a
  | [] => done
  | Cons x rest => reverseOnto (Cons x done) rest

test "an accumulator" := reverseOnto [] [1, 2, 3] == [3, 2, 1]
-- end accumulator

-- begin decreasing
def digits (n: Nat): List Nat
    decreasing n
:=
  if n < 10 then [n]
  else
    let rest := n / 10
    if smaller: rest < n then digits rest ++ [n % 10] else [n]

test "decreasing" := digits 2025 == [2, 0, 2, 5]
-- end decreasing

-- begin gcd
def gcd (a: Nat) (b: Nat): Nat
    decreasing b
:=
  if nonzero: b != 0 then
    if smaller: a % b < b then gcd b (a % b) else a
  else a

test "gcd" := gcd 84 36 == 12
-- end gcd

-- begin lexicographic
def ackermann (m: Nat) (n: Nat): Nat
    decreasing (m, n)
:=
  match m, n with
    | Zero, n => n + 1
    | Succ k, Zero => ackermann k 1 [decreasing := omega]
    | Succ k, Succ j => ackermann k (ackermann (Succ k) j [decreasing := omega]) [decreasing := omega]

test "ackermann" := ackermann 2 3 == 9
-- end lexicographic

-- begin mutual
def isEven: Nat -> Bool
  | 0 => True
  | Succ n => isOdd n

def isOdd: Nat -> Bool
  | 0 => False
  | Succ n => isEven n

test "mutual recursion" := isEven 10 && isOdd 7
-- end mutual

-- begin trees
type Tree =
  | Leaf
  | Node (left: Tree) (value: Nat) (right: Tree)

def Tree.insert (value: Nat): Tree -> Tree
  | Leaf => Node Leaf value Leaf
  | Node left here right =>
    if value < here then Node (left.insert value) here right
    else Node left here (right.insert value)

def Tree.toList: Tree -> List Nat
  | Leaf => []
  | Node left value right => left.toList ++ [value] ++ right.toList

def treeSort (values: List Nat): List Nat := (values.foldLeft (tree value => tree.insert value) Leaf).toList

test "tree sort" := treeSort [5, 2, 8, 1] == [1, 2, 5, 8]
-- end trees
