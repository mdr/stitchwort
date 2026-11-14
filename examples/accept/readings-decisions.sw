-- A fact about a decision's test, `d.holds = True` or `= False`, where the
-- decision doesn't compute (a hypothesis, or `==` through an instance in
-- scope) reads as the decision's proposition, `p` or `¬p`, through the
-- decision's own `sound` and `complete` and `Decidable.refute`; no
-- `@[reading]` is needed (docs/proposals/bool-as-proposition.md §5.4,
-- step 2).
import Std (Bool, Nat, Iff)

theorem holds ∀ [p: Prop] (d: Decidable p) (h: d.holds = True): p := h.read

theorem fails ∀ [p: Prop] (d: Decidable p) (h: d.holds = False): ¬p := h.read

-- `x == y` on a type known only by its `DecEq` reads as `x = y`, and as
-- `x ≠ y` when it is `False`.
theorem same ∀ [auto eq: DecEq a] (x y: a) (h: (x == y) = True): x = y := h.read

theorem differ ∀ [auto eq: DecEq a] (x y: a) (h: (x == y) = False): x ≠ y := h.read

-- Patterns read one layer at a time: `&&` as `∧`, then each side through
-- its decision.
theorem chain ∀ [auto eq: DecEq a] (x y z: a) (h: (x == y && y == z) = True): x = z := match h with
  | Both xy yz => rewrite xy.read, yz.read in rfl

-- A decision of `p ∧ q` is taken apart and built as `∧`.
theorem second ∀ [p q: Prop] (d: Decidable (p ∧ q)) (h: d.holds = True): q := match h with | Both _ y => y

theorem both ∀ [p q: Prop] (d: Decidable (p ∧ q)) (x: p) (y: q): d.holds = True := Both x y
