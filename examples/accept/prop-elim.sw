-- Pairs with soundness/or-elim.sw, hidden-type.sw and exists-witness.sw.

type And (p: Prop) (q: Prop): Prop =
  | Both (left: p) (right: q)

type Or (p: Prop) (q: Prop): Prop =
  | Inl (left: p)
  | Inr (right: q)

-- `And` has one constructor with only proof fields, so it may produce data.
def pick (p: Prop) (q: Prop): And p q → Nat
  | Both l r => 0

-- Matching on `Or` to produce another proof is fine.
theorem orComm (p: Prop) (q: Prop): Or p q → Or q p
  | Inl h => Inr h
  | Inr h => Inl h

type Exists (p: Nat → Prop): Prop =
  | Witness (x: Nat) (proof: p x)

-- Using the witness inside another proof is fine.
theorem existsSucc: Exists (n => n = n) → Exists (n => Succ n = Succ n)
  | Witness x h => Witness x rfl

-- Transport along an equality may produce data.
def transport [x y: a] (p: x = y) (f: a → Type) (fx: f x): f y := J (y' p' => f y') fx p
