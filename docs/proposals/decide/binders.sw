-- R1 (review-1.md §3): does `cases` care whether a statement's variables are
-- bound before or after the colon? Day 12's `rowEndsSplit`
-- (aoc/src/Aoc/Year2024/Day12/Proofs/Corners.sw:172), in four forms: two check today, two don't.
--
-- After the colon, as Corners.sw writes it, `:= cases` fails today:
--   theorem rowEndsAfter: (plot: Bool) → (out: Bool) → (side: Bool) → (sideOut: Bool) → … := cases
--   [E-CASES] Error: `cases` found nothing to split on, and nothing closes the goal
-- (the full output is in decide.md, §6.1.1). Binder introduction would make
-- it the same proof as `rowEndsLambda` below.
import Std (Bool, Nat, Void)

def convex (plot: Bool) (vertical: Bool) (horizontal: Bool): Bool := plot ∧ ¬vertical ∧ ¬horizontal
def concave (plot: Bool) (vertical: Bool) (horizontal: Bool) (diagonal: Bool): Bool := plot ∧ vertical ∧ horizontal ∧ ¬diagonal

-- Before the colon: checks.
theorem rowEndsBefore (plot: Bool) (out: Bool) (side: Bool) (sideOut: Bool):
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out) :=
  cases

-- After the colon, the binders introduced by hand with a lambda: checks.
-- This is the term binder introduction would build.
theorem rowEndsLambda: (plot: Bool) → (out: Bool) → (side: Bool) → (sideOut: Bool) →
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out) :=
  plot out side sideOut => cases

-- Split between the two: the binders before the colon are introduced, the
-- one after isn't, so this fails today too (in a comment):
--   theorem rowEndsMixed (plot: Bool) (out: Bool): (side: Bool) → (sideOut: Bool) → … := cases

-- Π goals `cases` proves today without introducing anything. Introduction
-- must not break them, which is why it comes after the closers (decide.md
-- §6.1.1): introduced first, `byHyp`'s goal would be `f a b = f b a`, which
-- no hypothesis is exactly, and it fails today in that form:
--   theorem byHypIntro (f: Bool → Bool → Bool) (same: …) (a: Bool) (b: Bool): f a b = f b a := cases
--   [E-CASES] Error: `cases` found nothing to split on, and nothing closes the goal
theorem byHyp (f: Bool → Bool → Bool) (same: (a: Bool) → (b: Bool) → f a b = f b a): (a: Bool) → (b: Bool) → f a b = f b a := cases

-- `omega` refutes the hypothesis of a goal `P → Void`.
theorem notLess (n: Nat): n + 1 < n → Void := cases

-- The term after `in` is tried against the whole goal.
theorem byTerm: (a: Bool) → (b: Bool) → (a ∨ b) = (b ∨ a) := cases in Bool.orComm

-- A leading implicit binder is introduced by the checker before `cases` runs.
theorem implicitAfter: [b: Bool] → not (not b) = b := cases
