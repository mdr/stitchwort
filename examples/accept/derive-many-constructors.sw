-- Derived `==` and `Ord` for types with two constructors or more compare the
-- constructors' positions first and the fields only for the same constructor,
-- so their size grows linearly with the number of constructors
-- (docs/proposals/derived-equality.md §5.6). The laws users rely on are the
-- same as ever: `DecEq.sound`, `DecEq.refl`, the readings, and `Ord`'s
-- `equal`, `flip` and `trans`.

import Std (DecEq, Eq, List, Nat, Ord, Ordering)

-- Recursive, nested in a list, with a proof field and a parameter.
type Node (a: Type) =
  | Leaf
  | Item (value: a)
  | Pair (left: Node a) (right: Node a)
  | Many (items: List (Node a))
  | Small (n: Nat) (ok: Nat.leq n 9 = True)
  | Named (name: Text) (body: Node a)

test "equal values" := Pair (Item 1) (Many [Leaf, Small 3 rfl]) == Pair (Item 1) (Many [Leaf, Small 3 rfl])
test "different fields" := !(Pair (Item 1) Leaf == Pair (Item 2) Leaf)
test "different constructors" := !(Item 1 == Leaf) && !((Many []: Node Nat) == Named "x" Leaf)
test "position first" := Leaf < Item 0 && Item 9 < Pair Leaf Leaf && (Small 9 rfl: Node Nat) < Named "" Leaf
test "then fields" := Item 1 < Item 2 && Many [Leaf] < Many [Leaf, Item 0] && !((Small 4 rfl: Node Nat) < Small 4 rfl)
test "sorts" := List.sort [Named "b" Leaf, Item 3, Leaf, Item 1] == [Leaf, Item 1, Item 3, Named "b" Leaf]

theorem sound ∀ (x y: Node Nat) (h: (x == y) = True): x = y := DecEq.sound h
theorem refl ∀ (x: Node Nat): (x == x) = True := DecEq.refl x
theorem read ∀ (x y: Node Nat) (h: (x == y) = False): x ≠ y := h.read
theorem compareEqual ∀ (x y: Node Text) (h: Ord.compare x y = Equal): x = y := Ord.equal x y h
theorem compareFlip ∀ (x y: Node Nat): Ord.compare y x = Ordering.flip (Ord.compare x y) := Ord.flip x y
theorem compareTrans ∀ (x y z: Node Nat)
    (h1: Ord.compare x y = Less)
    (h2: Ord.compare y z = Less):
    Ord.compare x z = Less :=
  Ord.trans x y z h1 h2

-- On constructors the tests still compute.
theorem computes: (Named "a" (Item 1) == Named "a" (Item 1)) = True := rfl
theorem computesApart: (Item 1 == Leaf) = False := rfl
theorem orders: Ord.compare (Pair Leaf (Item 2)) (Pair Leaf (Item 1)) = Greater := rfl

-- An enumeration's order is its tags'.
type Dir = | North | East | South | West

theorem dirSound ∀ (c d: Dir) (h: (c == d) = True): c = d := DecEq.sound h
theorem dirEqual ∀ (c d: Dir) (h: Ord.compare c d = Equal): c = d := Ord.equal c d h
test "directions" := North < West && !(South < East) && South == South
