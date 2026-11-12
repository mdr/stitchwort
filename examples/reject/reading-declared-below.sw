-- expect-error: E-NO-READING
-- A reading is used from where it is declared on: `below` takes `inRange`'s
-- fact apart before `inRangeReads` is declared, so the error says where the
-- reading is rather than reading the test as what it unfolds to.
import Std (Bool, Nat, Iff)

type InRange (lo x hi: Nat): Prop = { low: lo ≤ x, high: x ≤ hi }

def inRange (lo x hi: Nat): Bool := lo <= x && x <= hi

theorem below (lo x hi: Nat) (h: inRange lo x hi): x ≤ hi :=
  match h with
    | { low, high } => high

@[reading]
theorem inRangeReads (lo x hi: Nat): inRange lo x hi ↔ InRange lo x hi := {
  forward = h => { low = h.left, high = h.right },
  backward = r => Both r.low r.high
}
