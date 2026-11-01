-- expect-error: E-OMEGA
-- A `(p || q) = True` fact is split, and a `(p && q) = False` from the
-- goal's other side waits for the case that settles it (SW-997); but here
-- the `short` case doesn't last (`dx` may be positive), so `omega` still
-- fails, with a counterexample.
import Std (Bool, Int)

type Probe = { x: Int, dx: Int }

def overshot (right: Int) (probe: Probe): Bool := right < probe.x ∧ 0 ≤ probe.dx

def short (left: Int) (probe: Probe): Bool := probe.x < left

def past (left: Int) (right: Int) (probe: Probe): Bool := overshot right probe ∨ short left probe

def step (probe: Probe): Probe := { x = probe.x + probe.dx, dx = probe.dx }

theorem pastStays (left: Int) (right: Int) (probe: Probe) (h: past left right probe = True): past left right (step probe) = True := omega
