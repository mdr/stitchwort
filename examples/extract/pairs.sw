-- Functions that treat their fields differently, so mixing fields up in the
-- generated code would be noticed. Also: matching on two lists at once.
--
-- run: first (MkNatPair 1 2)
-- run: swap (MkNatPair 1 2)
-- run: zipSum [1, 2, 3] [10, 20]

import Std (Nat)

type NatPair: Type =
  | MkNatPair (left: Nat) (right: Nat)

export def first: NatPair -> Nat
  | MkNatPair a b => a

export def swap: NatPair -> NatPair
  | MkNatPair a b => MkNatPair b a

-- Two columns of constructor patterns.
export def zipSum: List Nat -> List Nat -> List Nat
  | Nil,       ys        => Nil
  | Cons x xs, Nil       => Nil
  | Cons x xs, Cons y ys => Cons (x + y) (zipSum xs ys)

-- Applies the prelude's `Nat.pred` to each element.
export def predecessors: List Nat -> List Nat
  | Nil       => Nil
  | Cons n ns => Cons (Nat.pred n) (predecessors ns)
