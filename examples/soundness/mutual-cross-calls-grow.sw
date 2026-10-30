-- expect-error: E-TERMINATION
-- Rocq CVE-2026-72703 (docs/research/kernel.md C26): a group whose only
-- calls are cross-calls, each on a larger argument. Rocq's guard checker
-- looked only at self-calls, so it took every parameter as uniform and
-- accepted this shape, giving `Void`. Size change closes the calls of the
-- whole group (`f → g → f` grows `n`). The kernel test is in
-- crates/core/tests/kernel_bugs_2026.rs. Neighbour: `countdown`/`step` in
-- accept/mutual.sw.
def f (n: Nat): Void := g (Succ n)

def g (n: Nat): Void := f (Succ n)

def proof: Void := f 0
