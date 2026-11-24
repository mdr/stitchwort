-- A theorem's proof may define its own helpers, and lemmas about them,
-- nested too, and use them anywhere inside the proof; outside it they
-- can't be named (D3736, examples/reject/proof-local-def-named-outside.sw).
import Std (Nat, Eq)

theorem addZeroTwice ∀ (n: Nat): n + 0 + 0 = n :=
  def addZero (m: Nat): Nat := m + 0
  theorem addZeroIs ∀ (m: Nat): addZero m = m := byComputing
  def twice (m: Nat): Nat :=
    def inner (k: Nat): Nat := addZero k
    inner (inner m)
  let both: twice n = n := byComputing
  both
