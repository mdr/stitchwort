-- expect-error: E-MUTUAL-PARAMETERS
-- Types defined together share one list of parameters, so the same ones
-- must be `auto` (docs/proposals/interfaces.md §7.5).

interface Ordered (k: Type) =
  { compare: k → k → Ordering }

type Tree (k: Type) [auto ord: Ordered k] =
  | Node (label: k) (kids: Forest k)

type Forest (k: Type) (ord: Ordered k) =
  | FNil
  | FCons (first: Tree k) (rest: Forest k ord)
