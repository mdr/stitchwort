-- `==`, `!=` and `if h: x = y` go through the `DecEq` interface
-- (docs/proposals/interfaces.md stage 2, §5.11, §5.12): the library's
-- instances, derived ones, and a module's own.

import Std (Bool, Eq, Vec)

-- Derived, for a type with a parameter: `[auto decEq: DecEq a]`.
type Tree (a: Type) =
  | Leaf
  | Node (left: Tree a) (value: a) (right: Tree a)

test "trees" := Node Leaf "x" Leaf == Node Leaf "x" Leaf
test "trees differ" := Node Leaf [1] Leaf != Node Leaf [2] Leaf

-- Generic code asks for `DecEq` like any interface, and `==` uses it.
def count [auto decEq: DecEq a] (x: a): List a -> Nat
  | Nil => 0
  | Cons y ys => (if x == y then 1 else 0) + count x ys

test "generic" := count (Node Leaf 1 Leaf) [Leaf, Node Leaf 1 Leaf, Node Leaf 1 Leaf] == 2

-- A module's own instance replaces the derived one (§5.11): nothing is
-- derived for `Colour`, and there's no overlap.
type Colour =
  | Red
  | Green

def anyColour (x: Colour) (y: Colour): Decidable (x = y) := match x, y with
  | Red, Red => Yes rfl
  | Green, Green => Yes rfl
  | Red, Green => No (e => Bool.falseNotTrue (Eq.cong isGreen e))
  | Green, Red => No (e => Bool.falseNotTrue (Eq.cong isRed e))

def isGreen: Colour -> Bool
  | Green => True
  | Red => False

def isRed: Colour -> Bool
  | Red => True
  | Green => False

instance Colour.instDecEq: DecEq Colour := { decide = anyColour }

test "own instance" := Red != Green && [Red] == [Red]

-- Vectors, by the library's instance.
def three: Vec Nat 2 := VCons 1 (VCons 2 VNil)

test "vectors" := three == VCons 1 (VCons 2 VNil)
test "vectors differ" := three != VCons 1 (VCons 3 VNil)

-- An `auto` proof of an equation uses a hypothesis first (D162): functions
-- have no `DecEq`, but `h` proves it.
def needsSame (f: Nat -> Nat) (g: Nat -> Nat) [auto ok: f = g]: Nat := f 1

def withProof (f: Nat -> Nat) (g: Nat -> Nat) (h: f = g): Nat := needsSame f g

test "hypothesis" := withProof (x => x + 1) (x => x + 1) rfl == 2

-- A decision procedure for anything else is an `instance` (D163).
type Token: Prop =
  | MkToken

instance decToken: Decidable Token := Yes MkToken

test "decided by an instance" := if Token then True else False
