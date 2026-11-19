-- A hypothesis whose type computes to a huge value (`grow 22 (Leaf x)`
-- written out has 2^22 nodes, over the 2 million a value read back may have)
-- that a proof step only carries along: a `rewrite` at another hypothesis, a
-- tuple `let` taking a lemma's proof of `∧` or `∃` apart, and a `match` on
-- an expression, which generalises over every hypothesis. Each reads the
-- context back, and where writing a call out is too large it is written as
-- the call, so none runs out of resources (SW-4091, SW-4113).
import Std (Eq, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

def double (n: Nat): Nat := n + n

theorem rewriteBeside ∀ (x z: Nat) (same: x = z) (q: Tree → Prop) (big: q (grow 22 (Leaf x))) (p: x = 1): z = 1 :=
  rewrite same at p then p

theorem twice ∀ (x: Nat) (h: double x = 4): double x = 4 ∧ double x = 4 := (h, h)

theorem letPairBeside ∀ (x: Nat) (q: Tree → Prop) (big: q (grow 22 (Leaf x))) (h: double x = 4): double x = 4 :=
  let (a, _) := twice x h
  a

theorem matchBeside ∀ (x: Nat) (q: Tree → Prop) (big: q (grow 22 (Leaf x))) (h: double x = 4): double x = 4 :=
  match double x with | _ => h

theorem someDouble ∀ (x: Nat): exists (y: Nat) => double x = y := (double x, byComputing)

theorem existsBeside ∀ (x: Nat) (q: Tree → Prop) (big: q (grow 22 (Leaf x))): exists (y: Nat) => double x = y :=
  let (y, e) := someDouble x
  (y, e)
