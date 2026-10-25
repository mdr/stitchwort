-- expect-error: E-INSTANCE-NONE
-- `Map (Nat -> Nat) Nat` needs an `Ordered (Nat -> Nat)` for its `ord`
-- parameter, and there's none.

interface Ordered (k: Type) =
  { compare: k → k → Ordering }

type Map (k: Type) (v: Type) [auto ord: Ordered k] =
  { entries: List (k, v) }

def table: Map (Nat → Nat) Nat := { entries = [] }
