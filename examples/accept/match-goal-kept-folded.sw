-- A `match` on an expression looks for it in the goal with the goal's
-- calls computed. A call that can't mention a variable of the
-- expression's computed form, and computes to something larger than it,
-- can't hide the expression, so the search reads it as the call
-- (SW-4637): `wide t` below has 2^16 leaves written out, and each `match`
-- read them all before. What the `match` does is unchanged.
import Std (Eq, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

def wide (t: Nat): Tree := grow 16 (Leaf t)

def double (n: Nat): Nat := n + n

-- The goal mentions `x` but holds `double x` nowhere, so the arm's goal is
-- the goal as it is.
theorem goalBeside ∀ (x t: Nat) (q: Tree → Nat → Prop) (big: ∀ (y: Nat) => q (wide t) y): q (wide t) x :=
  match double x with | n => big x

-- Named: the equation is bound, and there is still nothing to refine.
theorem goalBesideNamed ∀ (x t: Nat) (q: Tree → Nat → Prop) (big: ∀ (y: Nat) => q (wide t) y): q (wide t) x :=
  match h: double x with | n => big x

-- The goal holds `double x`, which is refined to `n` in the arm.
theorem goalRefined ∀ (x t: Nat) (q: Tree → Nat → Prop) (w: ∀ (n: Nat) => q (grow 4 (Leaf t)) n):
    q (grow 4 (Leaf t)) (double x) :=
  match double x with | n => w n
