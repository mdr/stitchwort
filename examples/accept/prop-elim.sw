-- Pairs with soundness/or-elim.sw, hidden-type.sw and exists-witness.sw.

type And (p : Prop) (q : Prop) : Prop =
  | Both (left : p) (right : q)

type Or (p : Prop) (q : Prop) : Prop =
  | Inl (left : p)
  | Inr (right : q)

-- `And` has one constructor with only proof fields, so it may produce data.
pick : (p : Prop) -> (q : Prop) -> And p q -> Nat
pick p q (Both l r) = 0

-- Matching on `Or` to produce another proof is fine.
theorem orComm : (p : Prop) -> (q : Prop) -> Or p q -> Or q p
orComm p q (Inl h) = Inr h
orComm p q (Inr h) = Inl h

type Exists (p : Nat -> Prop) : Prop =
  | Witness (x : Nat) (proof : p x)

-- Using the witness inside another proof is fine.
theorem existsSucc : Exists (\n -> n = n) -> Exists (\n -> Succ n = Succ n)
existsSucc (Witness x h) = Witness x rfl

-- Transport along an equality may produce data.
transport : [x y : a] -> x = y -> (f : a -> Type) -> f x -> f y
transport p f fx = J (\y' p' -> f y') fx p
