-- expect-error: E-MUTUAL-DATA
-- Data types that refer to each other aren't supported yet.
type Tree : Type =
  | Node (label : Nat) (kids : Forest)

type Forest : Type =
  | FNil
  | FCons (first : Tree) (rest : Forest)
