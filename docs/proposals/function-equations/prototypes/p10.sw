-- P10. A `Bool` guard's `else` stated in the complement form: `if fresh: b
-- = False` gives `fresh: b = True` (not `Not (b = False)`), as the
-- hand-written step lemmas chose (fillSkip, Graph.searchSkip).
import Std (Bool, Decidable, Eq, List, Nat, Void)

def countFresh: List Bool → Nat
  | Nil => 0
  | Cons b rest => if fresh: b = False then 1 + countFresh rest else countFresh rest

-- `countFresh.eq2.ifFalse`
theorem countFreshEq2IfFalse ∀ (b: Bool) (rest: List Bool)
    (fresh: b = True):
    countFresh (Cons b rest) = countFresh rest :=
  Decidable.elimEq _ _ _ _ (isFalse => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym fresh) isFalse))) (other =>
    rfl)

-- `countFresh.eq2.ifTrue`
theorem countFreshEq2IfTrue ∀ (b: Bool) (rest: List Bool)
    (fresh: b = False):
    countFresh (Cons b rest) = 1 + countFresh rest :=
  Decidable.elimEq _ _ _ _ (isFalse => rfl) (other => Void.exfalso (other fresh))
