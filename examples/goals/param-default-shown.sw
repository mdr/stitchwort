-- expect-error: E-REFL
-- A call that leaves a defaulted parameter out is shown as written, without
-- the argument its default fills: `range a b`, `scaled a`
-- (docs/proposals/signature-defaults.md §8.4). A default that is a constant
-- stays folded, as a named constant does, so it isn't shown either.

def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat := [start, stop, step]

def scaled (start: Nat) (factor: Nat := start * 2): Nat := start + factor

theorem rangeGoal (a: Nat) (b: Nat): range a b = [a, b, 1] := ?

theorem scaledGoal (a: Nat): scaled a = a + a * 2 := ?

theorem rangeShape (a: Nat) (b: Nat): range a b = [a, b, 2] := rfl

theorem scaledShape (a: Nat): scaled a = a := rfl

-- A local definition's calls are shown the same way.
def outer (k: Nat): Nat :=
  def inner (m: Nat) (extra: Nat := k + m): Nat := m + extra
  def innerGoal (m: Nat): inner m = m + (k + m) := ?
  inner 1
