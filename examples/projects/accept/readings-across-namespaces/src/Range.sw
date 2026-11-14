-- A test, and what it reads as, declared together.
namespace Range

type Within (lo x hi: Nat): Prop = { low: lo ≤ x, high: x ≤ hi }

def within (lo x hi: Nat): Bool := lo <= x && x <= hi

@[reading]
theorem withinReads ∀ (lo x hi: Nat): within lo x hi ↔ Within lo x hi :=
  { forward = h => { low = h.left, high = h.right }, backward = r => Both r.low r.high }
