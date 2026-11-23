-- A parameter whose type is stuck on something other than a call (a
-- record's type field, a cast, a quotient, a stuck `Quot.lift`) and holds a
-- call that computes to a huge value (`grow 22 (Leaf x)` written out has
-- 2^22 nodes, over the 2 million a value read back may have): whether it is
-- a proof is read off the type of what it's stuck on, without writing the
-- call out (SW-4671; as large-hypothesis-parameter.sw for a data type).
import Std (Eq, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

type Fam: Type 1 = { fam: Tree → Type, n: Nat }

type Wrap (t: Tree) = | MkWrap (n: Nat)

def size (f: Fam) (x: Nat) (w: f.fam (grow 22 (Leaf x))): Nat := x

def later (f: Fam) (x: Nat): f.fam (grow 22 (Leaf x)) → Nat := w => x

theorem same ∀ (f: Fam) (x: Nat) (w: f.fam (grow 22 (Leaf x))): x = x := byComputing

def underType (f: Fam) (x: Nat) (k: (t: Type) → f.fam (grow 22 (Leaf x))): Nat := x

def quotDom (x: Nat) (q: Quot (Wrap (grow 22 (Leaf x))) (u v => u = v)): Nat := x

def castDom (x: Nat) (h: Nat = Nat) (w: J (y p => Type) (Wrap (grow 22 (Leaf x))) h): Nat := x

theorem wrapRespects ∀ (u v: Tree) (e: u = v): Wrap (grow 22 u) = Wrap (grow 22 v) :=
  J (z p => Wrap (grow 22 u) = Wrap (grow 22 z)) byComputing e

def liftDom (q: Quot Tree (u v => u = v)) (w: Quot.lift [b := Type] (t => Wrap (grow 22 t)) wrapRespects q): Nat := 0
