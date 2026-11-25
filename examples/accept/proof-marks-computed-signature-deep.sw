-- A signature written through a definition (`def f: R`) has its
-- parameters' proof marks checked off the type computed, but only as far as
-- the body's lambdas (SW-4802): the result type past them, here a type that
-- takes a hundred thousand unfoldings to compute, is never normalised by the
-- reference build's validator, whose evaluator has no bound and would recurse
-- past the end of the stack. The kernel computes it, to check `5` against it.
-- differential: skip (a type a hundred thousand unfoldings deep is too deep for
-- the recursive reference evaluator)
import Std (Nat)

def Deep: Nat → Type
  | 0 => Nat
  | Succ n => Deep n

def R: Type := Nat → Deep 100000

def f: R := n => 5

def RProof: Type := (n: Nat) → n = n → Deep 100000

def g: RProof := n p => 5

def x: Deep 100000 := 5
