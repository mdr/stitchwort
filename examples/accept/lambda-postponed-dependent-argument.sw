-- A lambda whose parameter type comes from a later argument is checked last
-- even when a later parameter's type mentions it: that type holds a
-- placeholder for the lambda, which the argument given there solves. In
-- `memMapElim (e => e.fst.name) target pairs listed`, `pairs` fixes `e`'s
-- type and `listed`'s type says what the lambda is.

import Std (And, Exists, List, Nat, Void)

type Person = { name: Text }

def ann: Person := { name = "Ann" }

def applyChecked (f: a → Text) (same: f = f) (x: a): Text := f x

def name: Text := applyChecked (p => p.name) rfl ann

test "the lambda is checked after `ann`" := name == "Ann"

theorem memMapElim (f: a → b) (y: b): (xs: List a) → y ∈ xs.map f → Exists a (x => And (x ∈ xs) (f x = y))
  | Nil, member => Void.exfalso member
  | Cons x rest, Inl here => Witness x (Both (Inl rfl) here)
  | Cons x rest, Inr later =>
    Exists.elim (memMapElim f y rest later) (found both => Witness found (Both (Inr (And.left both)) (And.right both)))

theorem namedSomewhere (pairs: List (Person, Nat)) (target: Text) (listed: target ∈ pairs.map (e => e.fst.name)):
    Exists (Person, Nat) (e => And (e ∈ pairs) (e.fst.name = target)) :=
  memMapElim (e => e.fst.name) target pairs listed
