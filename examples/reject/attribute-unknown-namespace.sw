-- expect-error: E-ATTRIBUTE-UNKNOWN
-- Only `js.` attributes exist; bare names and other namespaces are reserved.
@[ts.name "ShapeDto"]
type Shape =
  | Circle (radius: Nat)
