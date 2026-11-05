-- expect-error: E-NO-EQUATION
-- A branch that computes on the proof of its `if h:` condition has no
-- equation when the condition isn't an equation of `Bool`s or a `DecEq` one:
-- `J` here computes on `h.left`, and two proofs of `a = b ∧ b = 0` aren't
-- convertible (D2180).
import Std (Nat, Eq)

def useAnd (a b n: Nat): Nat := if h: (a = b) ∧ (b = 0) then J (x e => Nat) n h.left else 0

theorem useAndEq (a b n: Nat) (h: (a = b) ∧ (b = 0)): useAnd a b n = n := useAnd.eq.ifTrue a b n h
