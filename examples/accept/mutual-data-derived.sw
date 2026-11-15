-- Derived `==`, `<` and `${…}` for types defined together, and for types
-- nested inside any earlier data type (docs/proposals/derived-equality.md
-- §5.3, §5.4). A syntax tree's types refer to each other: an expression
-- holds bodies, which hold statements, which hold expressions. They get
-- the same instances as any other type, with the same laws: `==` agrees
-- with `=` (`DecEq.sound`, `.read`), and `<` is an `Ord`. The group's
-- functions are defined together, one for each type and for each container
-- one of them is in (`List Item`, the program's own `Spaced Statement`),
-- so every call is on a part of the argument. An order or a display
-- through a container with an instance its module wrote itself, or a group
-- with one, isn't derived: reject/derived-through-own-instance.sw.

import Std (DecEq, List, NonEmptyList, Option, Ord, Ordering, Text)

-- A tree whose children are a forest, and a forest of trees.
type Tree = | Node (label: Nat) (kids: Forest)

type Forest = | FNil | FCons (first: Tree) (rest: Forest)

def leaf (n: Nat): Tree := Node n FNil

def tree: Tree := Node 1 (FCons (leaf 2) (FCons (Node 3 (FCons (leaf 4) FNil)) FNil))

test "tree equal" := tree == Node 1 (FCons (leaf 2) (FCons (Node 3 (FCons (leaf 4) FNil)) FNil))
test "tree unequal deep down" := tree != Node 1 (FCons (leaf 2) (FCons (Node 3 (FCons (leaf 5) FNil)) FNil))
test "forest unequal" := FCons (leaf 1) FNil != FNil
-- Constructors in the order they're declared, then the fields.
test "tree order" := Node 1 FNil < Node 1 (FCons (leaf 0) FNil) && Node 1 (FCons (leaf 9) FNil) < Node 2 FNil
test "forest order" := Ord.compare (FCons (leaf 2) FNil) (FCons (leaf 1) (FCons (leaf 0) FNil)) == Greater
test "tree show" := "${Node 1 (FCons (leaf 2) FNil)}" == "Node 1 (FCons (Node 2 FNil) FNil)"

-- The laws are the usual ones.
theorem treeSound ∀ (s t: Tree) (h: (s == t) = True): s = t := DecEq.sound h
theorem forestReads ∀ (s t: Forest) (h: (s == t) = True): s = t := h.read
theorem treeTrans ∀ (r s t: Tree) (h1: Ord.compare r s = Less) (h2: Ord.compare s t = Less): Ord.compare r t = Less :=
  Ord.trans r s t h1 h2
theorem computes: (leaf 1 == leaf 1) = True := rfl

-- Three types, two records among them, nested through `List`, `Option`
-- and a type of the program: the toy formatter's tree (tools/toyfmt).
type Comment = { text: Text }

-- A line of a list, and whether a blank line is above it.
type Spaced (a: Type) = { blankBefore: Bool, line: a }

type Expr =
  | Var (name: Text)
  | ListLiteral (items: List Item)
  | Call (callee: Expr) (arguments: List Item)
  | If (condition: Expr) (whenTrue: Body) (whenFalse: Body)

type Item = { comments: List Comment, value: Expr, trailing: Option Comment }

type Statement =
  | Let (name: Text) (body: Body)
  | Bare (value: Expr) (trailing: Option Comment)

type Body = { statements: List (Spaced Statement) }

def item (e: Expr): Item := { comments = [], value = e, trailing = None }

def bare (e: Expr): Body := { statements = [{ blankBefore = False, line = Bare e None }] }

def call: Expr := Call (Var "f") [item (Var "a"), item (ListLiteral [])]

def branch: Expr := If call (bare call) (bare (Var "b"))

test "expr equal" := branch == If call (bare call) (bare (Var "b"))
test "expr unequal in a body" := branch != If call (bare call) (bare (Var "c"))
test "item unequal" := item (Var "a") != { comments = [{ text = "-- a" }], value = Var "a", trailing = None }
test "body equal" := bare call == bare call
test "statement unequal" := Let "x" (bare call) != Bare call None
test "expr order" := Var "a" < Var "b" && Var "z" < call
test "body order" := bare (Var "a") < { statements = [{ blankBefore = True, line = Bare (Var "a") None }] }
test "body show" := "${bare (Var "a")}" == "{ statements = [{ blankBefore = False, line = Bare (Var \"a\") None }] }"
test "list order" := List.sort [Var "b", call, Var "a"] == [Var "a", Var "b", call]

theorem bodySound ∀ (s t: Body) (h: (s == t) = True): s = t := DecEq.sound h
theorem statementFlip ∀ (s t: Statement): Ord.compare t s = (Ord.compare s t).flip := Ord.flip s t

-- A group with a parameter: each type's instances take one for it.
type Rose (a: Type) = | Bloom (value: a) (kids: Roses a)

type Roses (a: Type) = | Bare0 | Grow (first: Rose a) (rest: Roses a)

def rose: Rose Nat := Bloom 1 (Grow (Bloom 2 Bare0) (Grow (Bloom 3 Bare0) Bare0))

test "rose equal" := rose == Bloom 1 (Grow (Bloom 2 Bare0) (Grow (Bloom 3 Bare0) Bare0))
test "rose unequal" := rose != Bloom 1 (Grow (Bloom 2 Bare0) Bare0)
test "rose order" := Bloom 1 Bare0 < rose && Bloom 'a' Bare0 < Bloom 'b' Bare0
test "rose show" := "${Bloom 'a' (Grow (Bloom 'b' Bare0) Bare0)}" == "Bloom 'a' (Grow (Bloom 'b' Bare0) Bare0)"

-- Nested through a library type outside the core. `NonEmptyList`'s module
-- writes its own `Ord` and `Show`, so only `==` is derived through it.
type Bunch = | Single (n: Nat) | Bunched (parts: NonEmptyList Bunch)

test "bunch equal" := Bunched { head = Single 1, tail = [Single 2] } == Bunched { head = Single 1, tail = [Single 2] }
test "bunch unequal" := Bunched { head = Single 1, tail = [] } != Bunched { head = Single 1, tail = [Single 2] }
