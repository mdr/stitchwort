-- expect-error: E-UNKNOWN-FIELD
-- A reading whose proof has an error is the only error reported: the uses
-- of its test that need it wait for it, rather than reading the test as
-- what it unfolds to.
import Std (Bool, Nat, Iff)

type InRange (lo x hi: Nat): Prop = { low: lo ≤ x, high: x ≤ hi }

def inRange (lo x hi: Nat): Bool := lo <= x && x <= hi

@[reading]
theorem inRangeReads (lo x hi: Nat): inRange lo x hi ↔ InRange lo x hi := {
  forward = h => { low = h.left, high = h.wrong },
  backward = r => Both r.low r.high
}

theorem below (lo x hi: Nat) (h: inRange lo x hi): x ≤ hi :=
  match h with
    | { low, high } => high

theorem high (x: Nat) (h: inRange 1 x 9): x ≤ 9 := h.read.high
