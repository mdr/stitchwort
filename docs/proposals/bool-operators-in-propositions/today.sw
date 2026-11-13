-- Probe for docs/proposals/bool-operators-in-propositions.md §2: the two
-- terms behind `a ∧ b` on `Bool`s, as they behave today.
-- Expected: one goal (`printed`), E-TYPE-MISMATCH at `closedProp`,
-- E-REWRITE-RULE at `rewriteProp`, one goal (`ifProof`); the rest check.
import Std (Bool, Nat, List)

theorem printed ∀ (a b: Bool) (fact: (a && b) = True) (prop: a = True ∧ b = True): Void := ?

theorem closedTest: (True && True) = True := rfl
theorem closedProp: True = True ∧ True = True := rfl

theorem rewriteTest ∀ (a b: Bool) (h: (a && b) = True): (if a && b then 1 else 2) = 1 :=
  rewrite h in rfl
theorem rewriteProp ∀ (a b: Bool) (h: a = True ∧ b = True): (if a && b then 1 else 2) = 1 :=
  rewrite h in rfl

theorem takeProp ∀ (a b: Bool) (h: a = True ∧ b = True): b = True := match h with | Both l r => r

def ifProof (a: Bool) (xs: List Nat) (i: Nat): Nat :=
  if h: a = True && i < xs.length then (let k: Void := ?; xs.getLt i) else 0
