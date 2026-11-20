-- metrics: guard-as-written: unchecked
-- A guard whose goal, generalised as written, doesn't type-check, so the
-- guard falls back to the goal read back unfolded (SW-4418). Here the goal
-- passes `scaled` a proof, `pickAtNonZero c`, whose type mentions `c == 0`
-- though the proof as written doesn't: abstracting the condition as written
-- gives `scaled 1 x (pickAtNonZero c)`, which wants `pick x ≠ 0`. Unfolded,
-- `scaled` computes and the proof is gone, so that motive checks and the arms
-- see `1 ≠ 0` and `2 ≠ 0`. What the failed attempt bound must be undone
-- first: left in place, the unfolded motive's levels were off by its
-- bindings and lifting the `match` panicked.
def pick (b: Bool): Nat := if b then 1 else 2

theorem pickNonZero ∀ (b: Bool): pick b ≠ 0 := match b with
  | True => Std.byDecision
  | False => Std.byDecision

theorem pickAtNonZero ∀ (c: Nat): pick (c == 0) ≠ 0 := pickNonZero (c == 0)

def scaled (n: Nat) (b: Bool) (ok: pick b ≠ 0): Nat := n * pick b

theorem scaledOne ∀ (c: Nat): scaled 1 (c == 0) (pickAtNonZero c) ≠ 0 := match c with
  | c if c == 0 => Std.byDecision
  | c => Std.byDecision
