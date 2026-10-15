-- expect-error: E-MUTUAL-SIGNATURE
-- A data type's parameters can only use what's finished before it, and types
-- defined together are finished together.
type Tree : Type =
  | Node (kids : (t : Tree) -> Forest t)

type Forest (t : Tree) : Type =
  | FNil
  | FCons (first : Tree) (rest : Forest t)
