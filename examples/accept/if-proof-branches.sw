-- An `if` may choose between proofs (SW-1015): `if h: P then a else b`
-- with proofs as branches is `Decidable.elimProof`, the `Prop` form of
-- `Decidable.elim`, with `h: P` in `a` and `h: Not P` in `b`. Being a proof,
-- it is erased like any other.

import Std (List, Nat, Void)

theorem split ∀ (m n: Nat): (m < n) ∨ (n <= m) := if h: m < n then Inl h else Inr omega

-- Nested, each branch with its own proof.
theorem trichotomy ∀ (m n: Nat): (m < n) ∨ ((m = n) ∨ (n < m)) :=
  if lt: m < n then Inl lt else if eq: m = n then Inr (Inl eq) else Inr (Inr omega)

-- With no binder, on a `Bool` or a decided proposition: the branches don't
-- see the condition's proof.
theorem onBool ∀ (b: Bool): 0 = 0 := if b then rfl else rfl

theorem onDecided ∀ (m: Nat) (rest: List Nat): 0 = 0 := if m < List.length rest then rfl else rfl

-- In a record's proof field, built at run time: only the number is computed.
type Capped = { value: Nat, capped: value <= 10 }

def cap (n: Nat): Capped :=
  if h: n <= 10 then { value = n, capped = h }
  else { value = 10, capped = if k: 10 <= 10 then k else Void.exfalso (k omega) }

test "cap keeps a small number" := (cap 7).value == 7

test "cap caps a large one" := (cap 70).value == 10
