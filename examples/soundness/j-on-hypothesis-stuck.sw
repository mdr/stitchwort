-- expect-error: E-REFL
-- Arena `k-rec-conv`, the reduction itself: a K-like rule would compute
-- `J` on any proof whose type looks like `a = a`, and a wrong one on
-- `h: 0 = y`. `J` computes only on `rfl` (docs/core.md, Equality), so
-- this transport is stuck. Neighbour: `kOnRfl` in
-- accept/kernel-2026-neighbours.sw.
theorem bad (y: Nat) (h: 0 = y): J (z _ => Nat) 5 h = 5 := rfl
