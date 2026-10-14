-- Functions that treat their fields differently, so mixing fields up in the
-- generated code would be noticed. Also: matching on two lists at once.
--
-- run: first (MkPair 1 2)
-- run: swap (MkPair 1 2)
-- run: zipSum [1, 2, 3] [10, 20]

type Pair : Type =
  | MkPair (left : Nat) (right : Nat)

export
first : Pair -> Nat
first (MkPair a b) = a

export
swap : Pair -> Pair
swap (MkPair a b) = MkPair b a

-- Two columns of constructor patterns.
export
zipSum : List Nat -> List Nat -> List Nat
zipSum Nil         ys          = Nil
zipSum (Cons x xs) Nil         = Nil
zipSum (Cons x xs) (Cons y ys) = Cons (x + y) (zipSum xs ys)

pred : Nat -> Nat
pred Zero     = Zero
pred (Succ k) = k

-- A nested match on a field.
export
predecessors : List Nat -> List Nat
predecessors Nil         = Nil
predecessors (Cons n ns) = Cons (pred n) (predecessors ns)
