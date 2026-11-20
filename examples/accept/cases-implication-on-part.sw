-- `cases` applies a hypothesis `P → Q` to a part of another hypothesis, a
-- side of a conjunction, where nothing else closes the case (SW-4472;
-- docs/syntax.md, "cases"). One application per implication, never chained,
-- and only to close the case there: `Q` is added beside the hypotheses and
-- the case is closed by a contradiction, a hypothesis, a part of one, or a
-- conjunction of those.
import Std (Nat)

theorem weaker ∀ (a b: Bool) (n: Nat) (implies: a = True → b = True) (both: a = True ∧ n = 3): b = True ∧ n = 3 := cases

-- The conjunction is what a definition computes to once its argument is
-- split (`Fmt.JoinProofs.endedWeaker`'s shape).
def Gate (open: Bool) (slot: Option Nat): Prop := match slot with
  | None => True
  | Some n => open = True ∧ n + 0 = n

theorem gateWeaker ∀ (a b: Bool) (implies: a = True → b = True) (slot: Option Nat) (gate: Gate a slot): Gate b slot :=
  cases
