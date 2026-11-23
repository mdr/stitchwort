-- expect-error: E-REFL
-- A transport along an `arithmetic` equation doesn't compute, even on numbers:
-- `arithmetic`'s proof is a call of the library's theorem `Omega.proveEq`,
-- which is sealed (D3722), so `J` is stuck on it. It moved here from
-- accept/omega-basics.sw, and becomes accepted again with rule K (a `J`
-- computes when the two sides of its equation are already equal, here
-- `7 * 3` and `7 + 7 + 7`; stage 4 of docs/proposals/full-proof-irrelevance.md).
import Std (Nat)

def transport (x n: Nat): Nat := J (y p => Nat) n (arithmetic: x * 3 = x + x + x)

theorem transportComputes: transport 7 42 = 42 := byComputing
