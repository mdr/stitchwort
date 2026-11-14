-- `cases` (docs/proposals/simp.md, stage 1): a proof by cases on whatever the
-- goal is stuck on, closing each case by computation, a contradiction, a
-- hypothesis or `omega`.
import Std (Bool, Float, Nat)

-- Truth tables: `cases` takes apart `a`, then `b`, and each case computes.
theorem orComm ∀ (a b: Bool): (a ∨ b) = (b ∨ a) := cases

theorem xorAssoc ∀ (a b c: Bool): Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c) := cases

-- A hypothesis stuck on something is split too: `a ∧ b` is `True` only when
-- both are, and the other cases contradict `h`. (A goal `a = True` needs no
-- split: `h` reads as `a ∧ b`, and its part `a` closes it.)
theorem andSwap ∀ (a b: Bool) (h: (a ∧ b) = True): (b ∧ a) = True := cases

theorem andLeft ∀ (a b: Bool) (h: (a ∧ b) = True): a = True := cases

-- Comparisons inside the conditions: each case left with arithmetic is
-- closed by `omega`.
def clamp (lo hi x: Nat): Nat := if x < lo then lo else if hi < x then hi else x

theorem clampBelow ∀ (lo hi x: Nat) (ordered: lo <= hi): clamp lo hi x <= hi := cases

-- IEEE order: `<` implies `<=`, with NaN, the two zeros and the sign of the
-- keys all taken apart, with no helper lemma.
theorem ieeeLtLe ∀ (x y: Float) (h: Float.ieeeLt x y = True): Float.ieeeLe x y = True := cases

-- `cases in t` closes every case `t` proves, and the others as `cases` would.
theorem ieeeLtLeBy ∀ (x y: Float) (h: Float.ieeeLt x y = True): Float.ieeeLe x y = True :=
  cases in Float.keyLessLeq _ _ h
