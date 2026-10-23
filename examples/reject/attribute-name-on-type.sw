-- expect-error: E-ATTRIBUTE
-- Renaming a type in the `.d.ts` is a later stage
-- (docs/proposals/attributes.md §9.1).
@[js.name "ShapeDto"]
type Shape =
  | Circle (radius: Nat)
