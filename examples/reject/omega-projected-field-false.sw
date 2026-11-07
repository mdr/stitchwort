-- expect-error: E-OMEGA
-- A field of an unknown record is an atom, so nothing is known of its value.
import Std (Nat)

type P = { x: Nat, y: Nat }

theorem fieldAtom (p: P): p.x + 1 ≤ p.y := omega
