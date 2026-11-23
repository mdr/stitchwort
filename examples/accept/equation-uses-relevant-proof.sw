-- A branch that computes on the proof of its `if h:` condition still has an
-- equation when the condition isn't an equation of `Bool`s or a `DecEq` one:
-- `J` here computes on `h.left`, and two proofs of `a = b ∧ b = 0` aren't
-- convertible, so the equation is proved along `Prop.irrel` (any two proofs
-- of a proposition are equal; D2180 refused it before std had that). The
-- equation keeps the `J`: `h.left` is a call of a sealed theorem.
import Std (Nat, Eq)

def useAnd (a b n: Nat): Nat := if h: (a = b) ∧ (b = 0) then J (x e => Nat) n h.left else 0

theorem useAndEq ∀ (a b n: Nat) (h: (a = b) ∧ (b = 0)): useAnd a b n = J (x e => Nat) n h.left :=
  useAnd.eq.ifTrue a b n h
