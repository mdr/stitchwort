-- expect-error: E-ABILITY
-- Landin's knot through a map: an operation storing a map whose values are
-- computations using the same ability. A map is data only when its values
-- are (docs/proposals/interfaces.md §7.5); its ordering doesn't change that.

import Std (Nat)

interface Ordered (k: Type) =
  { compare: k → k → Ordering }

instance Ordered.instNat: Ordered Nat :=
  { compare = Nat.compare }

type Map (k: Type) (v: Type) [auto ord: Ordered k] =
  { entries: List (k, v) }

ability Cell where
  write: Map Nat (() → {Cell} ()) → {Cell} ()
