-- Chapter 7: recursion and termination.
import Std (List, Nat, Set, Text)

-- begin structural
def length: List a → Nat
  | [] => 0
  | [_, ..rest] => 1 + length rest

def factorial: Nat → Nat
  | 0 => 1
  | Succ n => Succ n * factorial n

test "structural" := length [1, 2, 3] == 3 ∧ factorial 5 == 120
-- end structural

-- begin accumulator
def reverseOnto (done: List a): List a → List a
  | [] => done
  | [x, ..rest] => reverseOnto [x, ..done] rest

test "an accumulator" := reverseOnto [] [1, 2, 3] == [3, 2, 1]
-- end accumulator

-- begin decreasing
def digits (n: Nat): List Nat
    decreasing n
:=
  if n < 10 then [n] else digits (n / 10) ++ [n % 10]

test "decreasing" := digits 2025 == [2, 0, 2, 5]
-- end decreasing

-- begin gcd
def gcd (a: Nat) (b: Nat): Nat
    decreasing b
:=
  if a % b < b then gcd b (a % b) else a

test "gcd" := gcd 84 36 == 12
-- end gcd

-- begin match-fact
def total (set: Set Nat): Nat
    decreasing set.size
:= match found: set.popMin with
  | None => 0
  | Some (least, rest) => least + total rest [decreasing := Set.sizePopMin set least rest found]

test "total" := total [3, 1, 2].toSet == 6
-- end match-fact

-- begin lexicographic
def ackermann (m: Nat) (n: Nat): Nat
    decreasing (m, n)
:= match m, n with
  | Zero, n => n + 1
  | Succ k, Zero => ackermann k 1
  | Succ k, Succ j => ackermann k (ackermann (Succ k) j)

test "ackermann" := ackermann 2 3 == 9
-- end lexicographic

-- begin mutual
def isEven: Nat → Bool
  | 0 => True
  | Succ n => isOdd n

def isOdd: Nat → Bool
  | 0 => False
  | Succ n => isEven n

test "mutual recursion" := isEven 10 ∧ isOdd 7
-- end mutual

-- begin mutual-types
type Rose =
  | Branch (label: Nat) (kids: Roses)

type Roses =
  | RNil
  | RCons (first: Rose) (rest: Roses)

def Rose.total: Rose → Nat
  | Branch label kids => label + Roses.total kids

def Roses.total: Roses → Nat
  | RNil => 0
  | RCons first rest => Rose.total first + Roses.total rest

test "types that refer to each other" := Rose.total (Branch 1 (RCons (Branch 2 RNil) (RCons (Branch 3 RNil) RNil))) == 6
-- end mutual-types

-- begin nested
type Packet =
  | Number (value: Nat)
  | Packets (items: List Packet)

def Packet.depth (packet: Packet): Nat
    decreasing Packet.size packet
:= match packet with
  | Number n => 0
  | Packets items => 1 + (items.attach.map (e => Packet.depth e.value) |> .foldLeft 0 Nat.max)

test "depth" := Packet.depth (Packets [Number 1, Packets [Number 2, Packets [Number 3]], Packets []]) == 3
-- end nested

-- begin trees
type Tree =
  | Leaf
  | Node (left: Tree) (value: Nat) (right: Tree)

def Tree.insert (tree: Tree) (value: Nat): Tree := match tree with
  | Leaf => Node Leaf value Leaf
  | Node left here right =>
    if value < here then Node (left.insert value) here right
    else Node left here (right.insert value)

def Tree.toList: Tree → List Nat
  | Leaf => []
  | Node left value right => left.toList ++ [value] ++ right.toList

def treeSort (values: List Nat): List Nat := values.foldLeft Leaf Tree.insert |> .toList

test "tree sort" := treeSort [5, 2, 8, 1] == [1, 2, 5, 8]
-- end trees
