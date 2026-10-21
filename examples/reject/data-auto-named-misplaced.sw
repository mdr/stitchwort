-- expect-error: E-UNKNOWN-NAME
-- A type's `auto` parameter given by name goes in its place among the
-- parameters, as declared: `Map Nat Nat [ord := …]`
-- (docs/proposals/interfaces.md §7.5).

interface Ordered (k: Type) =
  { compare: k -> k -> Ordering }

instance Ordered.instNat: Ordered Nat :=
  { compare = Nat.compare }

type Map (k: Type) (v: Type) [auto ord: Ordered k] =
  { entries: List (k, v) }

def empty: Map [ord := Ordered.instNat] Nat Nat := { entries = [] }
