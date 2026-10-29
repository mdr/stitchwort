-- The shapes of nesting the kernel accepts
-- (docs/proposals/nested-data-types.md §5.2): a data type inside an earlier
-- data type, at parameters that one only stores. Each pairs with a must-reject
-- example in soundness/, named where it comes.

import Std (Eq,List, Nat, Option, Pair, Vec, Unit, And)

-- A rose tree with labels of any type: `Rose a` inside `List`.
type Rose (a: Type): Type =
  | Bloom (label: a) (kids: List (Rose a))

def Rose.count: Rose a → Nat
  | Bloom _ kids => Succ (Rose.countList kids)

def Rose.countList: List (Rose a) → Nat
  | Nil => 0
  | Cons t rest => Rose.count t + Rose.countList rest

theorem roseCount: Rose.count (Bloom 1 [Bloom 2 [], Bloom 3 [Bloom 4 []]]) = 4 := rfl

-- Nested twice, and in `Option` and a pair.
type Nest: Type =
  | Leaf
  | Deep (rows: List (List Nest))
  | Maybe (next: Option (Pair Nest Nat))

def Nest.depth: Nest → Nat
  | Leaf => 0
  | Deep rows => Succ (Nest.depthRows rows)
  | Maybe None => 1
  | Maybe (Some (MkPair n _)) => Succ (Nest.depth n)

def Nest.depthRows: List (List Nest) → Nat
  | Nil => 0
  | Cons row rest => Nat.max (Nest.depthRow row) (Nest.depthRows rest)

def Nest.depthRow: List Nest → Nat
  | Nil => 0
  | Cons n rest => Nat.max (Nest.depth n) (Nest.depthRow rest)

theorem nestDepth: Nest.depth (Deep [[Leaf], [Maybe (Some (MkPair (Deep []) 3))]]) = 3 := rfl

-- In `Vec`, at its parameter (its index, the length, is a number).
type Wide: Type =
  | Tip
  | Fork (kids: Vec Wide 2)

def Wide.tips: Wide → Nat
  | Tip => 1
  | Fork kids => Wide.tipsVec kids

def Wide.tipsVec: Vec Wide n → Nat
  | VNil => 0
  | VCons w rest => Wide.tips w + Wide.tipsVec rest

theorem wideTips: Wide.tips (Fork (VCons Tip (VCons (Fork (VCons Tip (VCons Tip VNil))) VNil))) = 3 := rfl

-- Two types defined together, both inside a list.
type Expr: Type =
  | Lit (value: Nat)
  | Block (body: List Stmt)

type Stmt: Type =
  | Assign (to: Nat) (value: Expr)
  | Seq (stmts: List Stmt)

def Expr.size: Expr → Nat
  | Lit _ => 1
  | Block body => Succ (Stmt.sizeList body)

def Stmt.size: Stmt → Nat
  | Assign _ e => Succ (Expr.size e)
  | Seq stmts => Succ (Stmt.sizeList stmts)

def Stmt.sizeList: List Stmt → Nat
  | Nil => 0
  | Cons s rest => Stmt.size s + Stmt.sizeList rest

theorem exprSize: Expr.size (Block [Assign 0 (Lit 1), Seq [Assign 1 (Block [])]]) = 6 := rfl

-- Inside a member of an earlier group of two: `Tree` and `Forest` are
-- defined together, and `Big` is inside `Tree`.
type Tree (a: Type): Type =
  | Node (label: a) (kids: Forest a)

type Forest (a: Type): Type =
  | FNil
  | FCons (first: Tree a) (rest: Forest a)

type Big: Type =
  | Small
  | Grown (tree: Tree Big)

def Big.count: Big → Nat
  | Small => 1
  | Grown t => Big.countTree t

def Big.countTree: Tree Big → Nat
  | Node b kids => Big.count b + Big.countForest kids

def Big.countForest: Forest Big → Nat
  | FNil => 0
  | FCons t rest => Big.countTree t + Big.countForest rest

theorem bigCount: Big.count (Grown (Node Small (FCons (Node (Grown (Node Small FNil)) FNil) FNil))) = 2 := rfl

-- An earlier field in the nested type's arguments: a tree whose index is
-- its height bound, with children one lower.
type Ranked: Nat → Type =
  | RLeaf: Ranked 0
  | RNode (n: Nat) (kids: List (Ranked n)): Ranked (Succ n)

def Ranked.count: Ranked n → Nat
  | RLeaf => 1
  | RNode _ kids => Succ (Ranked.countList kids)

def Ranked.countList: List (Ranked n) → Nat
  | Nil => 0
  | Cons t rest => Ranked.count t + Ranked.countList rest

theorem rankedCount: Ranked.count (RNode 1 [RNode 0 [], RNode 0 []]) = 3 := rfl

-- A predicate parameter: every branch is well typed, `All (t => Typed t r)`.
type All (a: Type) (p: a → Prop): List a → Prop =
  | AllNil: All a p []
  | AllCons (x: a) (xs: List a) (here: p x) (rest: All a p xs): All a p (Cons x xs)

type Term: Type =
  | Zero
  | Switch (branches: List Term)

type Ty: Type =
  | TNat

type Typed: Term → Ty → Prop =
  | TZero: Typed Zero TNat
  | TSwitch (bs: List Term) (r: Ty) (each: All Term (t => Typed t r) bs): Typed (Switch bs) r

theorem typedSwitch: Typed (Switch [Zero, Zero]) TNat :=
  TSwitch [Zero, Zero] TNat (AllCons Zero [Zero] TZero (AllCons Zero [] TZero AllNil))

-- Stored in an `Option`, it's in the option's value. Taken as the input of
-- a function on options, it would be negative: soundness/nested-input.sw.
type Stored: Type =
  | MkStored (next: Option Stored)

def Stored.depth: Stored → Nat
  | MkStored None => 0
  | MkStored (Some s) => Succ (Stored.depth s)

theorem storedDepth: Stored.depth (MkStored (Some (MkStored None))) = 1 := rfl

-- An equation between fields that don't hold the type, beside one that
-- does. An equation on fields that hold it is refused:
-- soundness/nested-recursive-field.sw.
type Checked: Type =
  | Check (n: Nat) (m: Nat) (same: n = m) (kids: List Checked)

def Checked.leaf (n: Nat): Checked := Check n n rfl []

-- `Option`'s parameter is nestable; `List.Member`'s isn't, since its other
-- parameter's type mentions it: soundness/nested-member.sw.
type Chain: Type =
  | Link (next: Option Chain) (label: Nat)

-- A proposition nested in `And` may be matched to produce a proof, but not
-- data: soundness/nested-prop-elim.sw.
type P: Prop =
  | MkP (h: And P Unit)

theorem fromP: P → Unit
  | MkP (Both _ u) => u
