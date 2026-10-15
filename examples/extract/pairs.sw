-- Functions that treat their fields differently, so mixing fields up in the
-- generated code would be noticed. Also: matching on two lists at once.
--
-- run: first (MkNatPair 1 2)
-- run: swap (MkNatPair 1 2)
-- run: zipSum [1, 2, 3] [10, 20]

type NatPair : Type =
  | MkNatPair (left : Nat) (right : Nat)

export
first : NatPair -> Nat
first (MkNatPair a b) = a

export
swap : NatPair -> NatPair
swap (MkNatPair a b) = MkNatPair b a

-- Two columns of constructor patterns.
export
zipSum : List Nat -> List Nat -> List Nat
zipSum Nil         ys          = Nil
zipSum (Cons x xs) Nil         = Nil
zipSum (Cons x xs) (Cons y ys) = Cons (x + y) (zipSum xs ys)

-- Applies the prelude's `pred` to each element.
export
predecessors : List Nat -> List Nat
predecessors Nil         = Nil
predecessors (Cons n ns) = Cons (pred n) (predecessors ns)
