-- A `Bool` `b` where a proposition is expected is the proposition `b = True`
-- (docs/proposals/bool-as-proposition.md §4): in a statement, a binder's
-- type, `if h:`, the operands of `∧ ∨ ¬ → ↔`, and an argument of type
-- `Prop`. It is the same term as writing `= True` out.
import Std (Bool, Nat, List, Iff)

def isSmall (n: Nat): Bool := n <= 3

theorem bare ∀ (b: Bool) (h: b): b = True := h

theorem written ∀ (b: Bool) (h: b = True): b := h

theorem call ∀ (n: Nat) (h: isSmall n): isSmall n = True := h

-- The operators stay logical; each `Bool` operand is coerced on its own.
theorem both ∀ (a b: Bool) (h: a ∧ b): a = True ∧ b = True := h

theorem mixed ∀ (n x: Nat) (h: isSmall n ∧ x < 3): x < 3 := h.right

theorem either ∀ (a b: Bool) (h: a): a ∨ b := Inl h

theorem neither ∀ (a: Bool) (h: ¬a): Not (a = True) := h

theorem implies ∀ (a b: Bool) (f: a → b) (h: a): b := f h

theorem iff ∀ (a: Bool): a ↔ a = True := Iff.refl _

theorem anyFact ∀ (xs: List Nat) (h: xs.any (x => x <= 3)): xs.any (x => x <= 3) = True := h

-- `if h: b` on a `Bool` gives `h: b` in the `then` branch.
def pick (b: Bool): Nat := if h: b then 1 else 2

theorem choose ∀ (b: Bool): b ∨ ¬b := if h: b then Inl h else Inr h

-- An argument whose type is `Prop`: the body of a lambda given for
-- `a → Prop`.
def holdsFor (p: Nat → Prop) (n: Nat): Prop := p n

theorem small: holdsFor (n => n <= 3) 2 := rfl

-- `∀` and `∃` bodies, and a `let` with a type.
theorem allSmall ∀ (h: ∀ (n: Nat) => isSmall n): isSmall 2 := (let k: isSmall 2 := h 2; k)
