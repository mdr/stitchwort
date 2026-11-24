-- expect-error: E-PROOF-PRIVATE
-- What a theorem's proof defines is private to that proof: the proof is
-- sealed, so `sumToZero.go` can't be named outside it (D3736). A local
-- definition of a `def` can be (`sumTo.go`, examples/accept/local-defs.sw).
import Std (Nat, Eq)

theorem sumToZero ∀ (n: Nat): n + 0 = n :=
  def go (m: Nat): Nat := m + 0
  let same: go n = n := byComputing
  same

theorem goOne: sumToZero.go 1 = 1 := byComputing
