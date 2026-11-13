-- SW-1600: in an arm of a named `match`, a lemma's `_` predicate is fixed
-- by what's expected of the lemma's result, not by rewriting the equation
-- `isReady: gate.ready bound = True` into `True = True`, which would solve
-- it as `x => True`.
import Std (List)

type Gate = { left: Nat, right: Nat }

def Gate.ready (gate: Gate) (bound: Nat): Bool := gate.left < bound

theorem keep ∀ (bound: Nat) (gate: Gate) (gates: List Gate) (kept: gate ∈ gates.filter (other => other.ready bound)): gate ∈ gates :=
  (List.memFilter gates _ kept).left

theorem readyKept ∀ (bound: Nat) (gates: List Gate): ∀ (gate: Gate) => gate ∈ gates → gate ∈ gates :=
  (gate member =>
    match isReady: gate.ready bound with
      | True => keep bound gate gates (List.memFilterIntro gates _ member isReady)
      | False => member)
