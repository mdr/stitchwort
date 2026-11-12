-- Which uses of a test see its reading is decided by what depends on
-- what, not by where things are written (D3537): `below` is checked after
-- `inRangeReads`, which it doesn't depend on, so it reads `inRange` as
-- `InRange`. `fwd`, which the reading's own proof uses, reads `inRange` as
-- what it unfolds to, `lo <= x && x <= hi`, as the reading's proof does.
import Std (Bool, Nat, Iff)

type InRange (lo x hi: Nat): Prop = { low: lo ≤ x, high: x ≤ hi }

def inRange (lo x hi: Nat): Bool := lo <= x && x <= hi

theorem below (lo x hi: Nat) (h: inRange lo x hi): x ≤ hi :=
  match h with
    | { low, high } => high

theorem fwd (lo x hi: Nat) (h: inRange lo x hi): InRange lo x hi := { low = h.left, high = h.right }

@[reading]
theorem inRangeReads (lo x hi: Nat): inRange lo x hi ↔ InRange lo x hi := {
  forward = fwd lo x hi,
  backward = r => Both r.low r.high
}
