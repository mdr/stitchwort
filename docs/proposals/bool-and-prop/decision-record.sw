-- Probe for docs/proposals/bool-and-prop.md §7.2: a decision as a `Bool`
-- with its two proofs (Agda's `Dec`), instead of `Yes proof | No refutation`.
-- Checks.
import Std (Bool, Nat)

type Dec (p: Prop) = { does: Bool, sound: does = True → p, complete: p → does = True }

def decLe (m n: Nat): Dec (m ≤ n) := { does = Nat.leq m n, sound = h => h, complete = h => h }

def Dec.and [p q: Prop] (dp: Dec p) (dq: Dec q): Dec (p ∧ q) := {
  does = dp.does && dq.does,
  sound = h => Both (dp.sound (Bool.andLeft h)) (dq.sound (Bool.andRight h)),
  complete = h => Bool.andIntro (dp.complete h.left) (dq.complete h.right)
}

-- The decision's `Bool` is the test, by computation, with the numbers unknown.
theorem doesIsLeq ∀ (m n: Nat): (decLe m n).does = Nat.leq m n := rfl
theorem andDoesIsAnd ∀ (a b c d: Nat): (Dec.and (decLe a b) (decLe c d)).does = (Nat.leq a b && Nat.leq c d) := rfl

-- A proof by running the test, at any size.
theorem byTest: 3 ≤ 5 ∧ 123456789012345678901234567890 ≤ 123456789012345678901234567891 :=
  (Dec.and (decLe 3 5) (decLe 123456789012345678901234567890 123456789012345678901234567891)).sound rfl

-- One `if`: with or without the proof in its branches, it tests the same `Bool`.
def elimEq [a: Type]: (c: Bool) → (ifTrue: c = True → a) → (ifFalse: c = False → a) → a
  | True, y, n => y rfl
  | False, y, n => n rfl

def clamp (lo x: Nat): Nat := Bool.ifThenElse (decLe lo x).does (_ => x) (_ => lo)
def safeSub (a b: Nat): Nat := elimEq (decLe b a).does (h => a - b) (h => 0)

theorem clampGe ∀ (lo x: Nat): lo ≤ clamp lo x := match h: Nat.leq lo x with
  | True => h
  | False => Nat.leRefl lo
theorem safeSubLe ∀ (a b: Nat) (h: b ≤ a): safeSub a b = a - b := rewrite h in rfl
