-- expect-error: E-TYPE-MISMATCH
-- A map built with a named alternative ordering, passed where the parameter's
-- type names the instance's: the ordering is part of the map's type, so the
-- types differ (docs/proposals/interfaces.md §7.5), and the note says so.

import Std (Nat)

interface Ordered (k: Type) =
  { compare: k → k → Ordering }

instance Ordered.instNat: Ordered Nat :=
  { compare = Nat.compare }

def descending: Ordered Nat := { compare = m n => Nat.compare n m }

type Map (k: Type) (v: Type) [auto ord: Ordered k] =
  { entries: List (k, v) }

def size (m: Map Nat Nat): Nat := m.entries.length

def down: Map Nat Nat [ord := descending] := { entries = [] }

def wrong: Nat := size down
