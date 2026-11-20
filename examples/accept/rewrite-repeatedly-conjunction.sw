-- `rewrite repeatedly` closes a conjunction whose parts each close on their
-- own: by computing, by contradicting hypotheses, by a hypothesis or a part
-- of one, or as a conjunction of such parts in turn (SW-4472; docs/syntax.md,
-- "rewrite repeatedly"). The whole conjunction is no equation, so computing
-- alone can't close it. The proof is the pair of the parts' proofs.
import Std (Nat)

-- Each part computes once the rules have rewritten it.
theorem parts ∀ (s: Text) (n: Nat) (isOpen: s = "(") (two: n = 2): (s == "(") = True ∧ n + 1 = 3 ∧ True = True :=
  rewrite repeatedly [isOpen, two]

-- A part a hypothesis proves, beside one that computes.
theorem withHypothesis ∀ (p: Nat → Prop) (n m: Nat) (holds: p m) (same: n = m): p n ∧ n + 0 = m :=
  rewrite repeatedly [same]
