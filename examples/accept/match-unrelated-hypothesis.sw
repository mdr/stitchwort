-- A `match` on an expression generalises the goal and every hypothesis
-- whose type holds the expression. A hypothesis that can't hold it, since
-- its type doesn't mention a variable the expression certainly computes
-- to something mentioning, isn't read back at all (SW-4635): `big` below
-- has 2^16 leaves written out, and each `match` and tuple `let` read it
-- back before. Hypotheses that do hold the expression are refined as
-- before.
import Std (Eq, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

def double (n: Nat): Nat := n + n

theorem someDouble ∀ (x: Nat): exists (y: Nat) => double x = y := (double x, byComputing)

-- `big` mentions `t`, and `someDouble x` only `x`.
theorem existsUnrelated ∀ (x t: Nat) (q: Tree → Prop) (big: q (grow 16 (Leaf t))): exists (y: Nat) => double x = y :=
  let (y, e) := someDouble x
  (y, e)

-- `h` holds `double x` and is refined to `n = 4`, as the goal is; `big` is
-- carried as it is, unread. (The goal is always read: one holding `big`'s
-- type would be read back whole.)
theorem refinedBeside ∀ (x t: Nat) (q: Tree → Prop) (big: q (grow 16 (Leaf t))) (h: double x = 4): double x = 4 :=
  match double x with | n => h

-- A hypothesis about a variable whose type holds the expression is
-- refined along with it.
theorem dependentRefined ∀ (x t: Nat) (q: Tree → Prop) (big: q (grow 16 (Leaf t))) (p: Nat → Prop)
    (w: p (double x)) (keep: p (double x) → p (double x)):
    p (double x) :=
  match double x with | n => keep w

-- A closed expression may occur anywhere, so every type is read.
theorem closedRefined ∀ (q: Tree → Prop) (big: q (grow 4 (Leaf 2))) (h: double 2 = 4): double 2 = 4 :=
  match double 2 with | n => h
