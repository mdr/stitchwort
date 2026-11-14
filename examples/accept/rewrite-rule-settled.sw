-- A `rewrite` rule holding a record literal whose type only its field
-- names say (docs/proposals/postponement.md, invariant 7 restated, D2087).
-- The rule is elaborated with no expected type, so `{ label = 3 }` waits
-- for its type, and the rule's left side would be `keep ?` with nothing to
-- look for. The rule's own waiting checks are settled before its search,
-- defaults included, and only those: the field-name rule makes it a `Tag`,
-- and `keep { label = 3 }` is found in the goal.
import Std (Eq, Nat)

type Tag = { label: Nat }

def keep (a: t): t := a

theorem keepSame ∀ (a: t): keep a = a := rfl

theorem kept: keep { label = 3 } = ({ label = 3 }: Tag) := rewrite keepSame { label = 3 } in rfl

-- With the literal's type written, nothing waits.
theorem annotated: keep { label = 3 } = ({ label = 3 }: Tag) := rewrite keepSame ({ label = 3 }: Tag) in rfl
