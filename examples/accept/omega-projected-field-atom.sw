-- `arithmetic` takes a field of an unknown record (`p.x`) as an atom, as it does
-- any term it cannot see into: it proves what holds whatever the field is.

import Std (Nat)

type P = { x: Nat, y: Nat }

theorem fieldAtom ∀ (p: P): p.x ≤ p.x + 1 := arithmetic

theorem fieldsApart ∀ (p: P) (h: p.x < p.y): p.x + 1 ≤ p.y := arithmetic
