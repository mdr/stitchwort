-- expect-error: E-INSTANCE-HEAD
-- In an instance head, a type's `auto` parameter is written as a variable,
-- `Pretty (Map k v [ord := o])`, so the instance covers every ordering and
-- matching fixes it (docs/proposals/interfaces.md §7.5). It's never found
-- there, so leaving it out is an error, saying what to write.

interface Ordered (k: Type) =
  { compare: k → k → Ordering }

interface Pretty (a: Type) =
  { pretty: a → Text }

type Map (k: Type) (v: Type) [auto ord: Ordered k] =
  { entries: List (k, v) }

instance Map.instPretty: Pretty (Map k v) :=
  { pretty = m => "map" }
