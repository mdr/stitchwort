-- expect-error: E-JS-NAME-CLASH
-- A type with attributes is checked where it's declared: here the field
-- `kind` would have the key that says which constructor an object is.
@[js.tag "kind"]
type Shape =
  | Circle (kind: Text) (radius: Nat)
