-- expect-error: E-REFL
-- Lean Kernel Arena `k-rec-conv` (docs/research/kernel.md C24): a checker
-- with a wrong K-like reduction equated `x => x` with `_ => y`. Here K is
-- a unification rule (deletion), never a reduction, so the two functions
-- differ at a fresh variable. The kernel test is in
-- crates/core/tests/kernel_bugs_2026.rs. Neighbour: `kOnRfl` in
-- accept/kernel-2026-neighbours.sw.
theorem bad (y: Nat): ((x: Nat) => x) = ((z: Nat) => y) := rfl
