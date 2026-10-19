-- expect-error: E-MUTUAL-CONSTRUCTOR
-- A field can mention a type defined together with its own, but not that
-- type's constructors: none of them exists until every field is finished.
-- Pairs with accept/mutual-data.sw.
type Tree: Type =
  | Node (kids: Forest) (ok: kids = FNil)

type Forest: Type =
  | FNil
  | FCons (first: Tree) (rest: Forest)
