-- A hole checked against a call of a `Prop` definition shows the call, as
-- written, not the `∧` or `∀` it unfolds to: in a `match`'s arms too, where
-- the arm's own goal is `Small (if True then n else 0)`.
def Small (n: Nat): Prop := n ≤ 3 ∧ n ≠ 7

theorem top ∀ (n: Nat): Small n := ?

theorem viaMatch ∀ (b: Bool) (n: Nat): Small (if b then n else 0) := match b with
  | True => ?
  | False => ?
